// mugda-engine.js
// Complete port of Karl Mehltretter's Mugda (Lexer, Parser, ScopeChecker, Value,
// SPos, Completness, Termination, TypeChecker) with live toggle between:
//   - mode: 'fixed' (Bug-Fixed Mugda)
//   - mode: '2008'  (Original April 2008 Mugda v1.0)

(function (root, factory) {
  if (typeof module === 'object' && module.exports) {
    module.exports = factory();
  } else {
    root.MugdaEngine = factory();
  }
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  // =========================================================================
  // 1. LEXER
  // =========================================================================
  const KEYWORDS = new Set([
    'Set', 'Size', 'data', 'codata', 'fun', 'cofun',
    'let', 'in', 'mutual', 'eval', 'sized'
  ]);

  function tokenize(input) {
    let i = 0;
    let line = 1;
    let col = 1;
    const tokens = [];

    function adv(n = 1) {
      for (let k = 0; k < n; k++) {
        if (input[i] === '\n') { line++; col = 1; }
        else { col++; }
        i++;
      }
    }

    while (i < input.length) {
      const ch = input[i];
      if (/\s/.test(ch)) {
        adv();
        continue;
      }
      if (input.startsWith('--', i)) {
        while (i < input.length && input[i] !== '\n') adv();
        continue;
      }
      if (input.startsWith('{-', i)) {
        let depth = 1;
        adv(2);
        while (i < input.length && depth > 0) {
          if (input.startsWith('{-', i)) { depth++; adv(2); }
          else if (input.startsWith('-}', i)) { depth--; adv(2); }
          else adv();
        }
        continue;
      }
      const tl = line, tc = col;
      if (input.startsWith('->', i)) {
        tokens.push({ type: 'ARROW', val: '->', line: tl, col: tc });
        adv(2);
        continue;
      }
      const single = {
        '\\': 'LAMBDA', ':': 'COLON', ';': 'SEMI',
        '(': 'LPAREN', ')': 'RPAREN', '{': 'LBRACE', '}': 'RBRACE',
        '=': 'EQ', '+': 'PLUS', '-': 'MINUS', '.': 'DOT',
        '$': 'SUCC', '#': 'INFTY'
      };
      if (single[ch]) {
        tokens.push({ type: single[ch], val: ch, line: tl, col: tc });
        adv();
        continue;
      }
      if (/[A-Za-z0-9_']/.test(ch)) {
        let s = '';
        while (i < input.length && /[A-Za-z0-9_']/.test(input[i])) {
          s += input[i];
          adv();
        }
        // `const` is a synonym for `let`, as in Mugda/Core.lean (the 2008 Haskell lexer had no `const`).
        const type = s === 'const' ? 'LET' : (KEYWORDS.has(s) ? s.toUpperCase() : 'IDENT');
        tokens.push({ type, val: s, line: tl, col: tc });
        continue;
      }
      throw new Error(`Lexical error at line ${tl}, col ${tc}: unexpected character '${ch}'`);
    }
    tokens.push({ type: 'EOF', val: '', line, col });
    return tokens;
  }

  // =========================================================================
  // 2. PARSER (Concrete Syntax)
  // =========================================================================
  function parse(input) {
    const tokens = tokenize(input);
    let pos = 0;

    function peek(offset = 0) { return tokens[pos + offset] || tokens[tokens.length - 1]; }
    function eat(type) {
      const t = peek();
      if (t.type !== type) {
        throw new Error(`Parse error at token "${t.val || t.type}" at line ${t.line}, col ${t.col} (expected ${type})`);
      }
      pos++;
      return t;
    }

    function parseDecls() {
      const decls = [];
      while (peek().type !== 'EOF' && peek().type !== 'RBRACE') {
        while (peek().type === 'SEMI') eat('SEMI');
        if (peek().type === 'EOF' || peek().type === 'RBRACE') break;
        decls.push(parseDecl());
        while (peek().type === 'SEMI') eat('SEMI');
      }
      return decls;
    }

    function parseDecl() {
      const t = peek();
      if (t.type === 'SIZED') {
        eat('SIZED');
        const co = peek().type === 'CODATA' ? (eat('CODATA'), 'CoInd') : (eat('DATA'), 'Ind');
        return parseDataRest(co, 'Sized');
      }
      if (t.type === 'DATA') { eat('DATA'); return parseDataRest('Ind', 'NotSized'); }
      if (t.type === 'CODATA') { eat('CODATA'); return parseDataRest('CoInd', 'NotSized'); }
      if (t.type === 'FUN') { eat('FUN'); return parseFunRest('Ind'); }
      if (t.type === 'COFUN') { eat('COFUN'); return parseFunRest('CoInd'); }
      if (t.type === 'EVAL') {
        eat('EVAL'); eat('LET');
        const name = eat('IDENT').val;
        eat('COLON');
        const ty = parseExpr();
        eat('EQ');
        const body = parseExpr();
        return { tag: 'LetDecl', evalFlag: true, ts: { name, ty }, body };
      }
      if (t.type === 'LET') {
        eat('LET');
        const name = eat('IDENT').val;
        eat('COLON');
        const ty = parseExpr();
        eat('EQ');
        const body = parseExpr();
        return { tag: 'LetDecl', evalFlag: false, ts: { name, ty }, body };
      }
      if (t.type === 'MUTUAL') {
        eat('MUTUAL');
        eat('LBRACE');
        const subs = parseDecls();
        eat('RBRACE');
        return { tag: 'MutualDecl', decls: subs };
      }
      throw new Error(`Parse error at token "${t.val}" at line ${t.line}, col ${t.col}`);
    }

    function parseDataRest(co, sz) {
      const name = eat('IDENT').val;
      const params = [];
      while (peek().type === 'LPAREN') {
        eat('LPAREN');
        let p = 'Not';
        if (peek().type === 'PLUS') { eat('PLUS'); p = 'SPos'; }
        else if (peek().type === 'MINUS') { eat('MINUS'); p = 'Not'; }
        const pname = eat('IDENT').val;
        eat('COLON');
        const pty = parseExpr();
        eat('RPAREN');
        params.push({ pos: p, name: pname, ty: pty });
      }
      eat('COLON');
      const ty = parseExpr();
      eat('LBRACE');
      const cons = [];
      while (peek().type !== 'RBRACE' && peek().type !== 'EOF') {
        while (peek().type === 'SEMI') eat('SEMI');
        if (peek().type === 'RBRACE') break;
        const cname = eat('IDENT').val;
        eat('COLON');
        const cty = parseExpr();
        cons.push({ name: cname, ty: cty });
        while (peek().type === 'SEMI') eat('SEMI');
      }
      eat('RBRACE');
      return { tag: 'DataDecl', co, sz, ts: { name, ty }, params, cons };
    }

    function parseFunRest(co) {
      const name = eat('IDENT').val;
      eat('COLON');
      const ty = parseExpr();
      eat('LBRACE');
      const clauses = [];
      while (peek().type !== 'RBRACE' && peek().type !== 'EOF') {
        while (peek().type === 'SEMI') eat('SEMI');
        if (peek().type === 'RBRACE') break;
        const fname = eat('IDENT').val;
        const pats = [];
        while (peek().type !== 'EQ' && peek().type !== 'EOF') {
          pats.push(parseAtomPat());
        }
        eat('EQ');
        const rhs = parseExpr();
        clauses.push({ fname, pats, rhs });
        while (peek().type === 'SEMI') eat('SEMI');
      }
      eat('RBRACE');
      return { tag: 'FunDecl', co, ts: { name, ty }, clauses };
    }

    function parseAtomPat() {
      const t = peek();
      if (t.type === 'IDENT') {
        eat('IDENT');
        return { tag: 'IdentP', name: t.val, args: [] };
      }
      if (t.type === 'DOT') {
        eat('DOT');
        const e = parseAtomExpr();
        return { tag: 'DotP', expr: e };
      }
      if (t.type === 'LPAREN') {
        eat('LPAREN');
        const p = parseInnerPat();
        eat('RPAREN');
        return p;
      }
      throw new Error(`Parse error in pattern at token "${t.val}" at line ${t.line}, col ${t.col}`);
    }

    function parseInnerPat() {
      if (peek().type === 'SUCC') {
        eat('SUCC');
        const sub = (peek().type === 'SUCC') ? parseInnerPat() : parseAtomPat();
        return { tag: 'SuccP', pat: sub };
      }
      if (peek().type === 'DOT') {
        return parseAtomPat();
      }
      if (peek().type === 'LPAREN') {
        eat('LPAREN');
        const p = parseInnerPat();
        eat('RPAREN');
        return p;
      }
      const name = eat('IDENT').val;
      const args = [];
      while (peek().type !== 'RPAREN' && peek().type !== 'EOF') {
        args.push(parseAtomPat());
      }
      return { tag: 'IdentP', name, args };
    }

    function isDomainParen() {
      if (peek().type !== 'LPAREN') return false;
      if (peek(1).type === 'IDENT' && peek(2).type === 'COLON') {
        // Scan matching RPAREN
        let depth = 0;
        let k = 0;
        while (peek(k).type !== 'EOF') {
          if (peek(k).type === 'LPAREN') depth++;
          else if (peek(k).type === 'RPAREN') {
            depth--;
            if (depth === 0) {
              return peek(k + 1).type === 'ARROW';
            }
          }
          k++;
        }
      }
      return false;
    }

    function parseExpr() {
      if (peek().type === 'LAMBDA') {
        eat('LAMBDA');
        const x = eat('IDENT').val;
        eat('ARROW');
        const body = parseExpr();
        return { tag: 'Lam', name: x, body };
      }
      if (peek().type === 'LET') {
        eat('LET');
        const x = eat('IDENT').val;
        eat('COLON');
        const ty = parseExpr();
        eat('EQ');
        const e1 = parseExpr();
        eat('IN');
        const e2 = parseExpr();
        return { tag: 'LLet', name: x, ty, e1, e2 };
      }
      if (isDomainParen()) {
        eat('LPAREN');
        const x = eat('IDENT').val;
        eat('COLON');
        const dom = parseExpr();
        eat('RPAREN');
        eat('ARROW');
        const cod = parseExpr();
        return { tag: 'Pi', name: x, dom, cod };
      }
      const left = parseAppExpr();
      if (peek().type === 'ARROW') {
        eat('ARROW');
        const right = parseExpr();
        return { tag: 'Pi', name: '', dom: left, cod: right };
      }
      return left;
    }

    function parseAppExpr() {
      const atoms = [];
      while (true) {
        const t = peek();
        if (
          t.type === 'IDENT' || t.type === 'SET' || t.type === 'SIZE' ||
          t.type === 'INFTY' || t.type === 'SUCC' ||
          (t.type === 'LPAREN' && !isDomainParen())
        ) {
          atoms.push(parseAtomExpr());
        } else {
          break;
        }
      }
      if (atoms.length === 0) {
        const t = peek();
        throw new Error(`Parse error in expression at token "${t.val || t.type}" at line ${t.line}, col ${t.col}`);
      }
      // Resolve `$` (Succ) prefix application just like Happy grammar (`$` binds to following atom or `$ ...`)
      function buildApp(list) {
        // Fold from left, except Succ consumes the rest of a Succ chain or single atom
        const processed = [];
        for (let idx = 0; idx < list.length; idx++) {
          if (list[idx].tag === 'SuccMarker') {
            if (idx + 1 >= list.length) throw new Error('Parse error: trailing $');
            // Check how many consecutive $ there are
            let count = 0;
            while (idx < list.length && list[idx].tag === 'SuccMarker') {
              count++;
              idx++;
            }
            if (idx >= list.length) throw new Error('Parse error: trailing $');
            let arg = list[idx];
            for (let c = 0; c < count; c++) {
              arg = { tag: 'Succ', expr: arg };
            }
            processed.push(arg);
          } else {
            processed.push(list[idx]);
          }
        }
        if (processed.length === 1) return processed[0];
        return { tag: 'App', fn: processed[0], args: processed.slice(1) };
      }
      return buildApp(atoms);
    }

    function parseAtomExpr() {
      const t = peek();
      if (t.type === 'IDENT') { eat('IDENT'); return { tag: 'Ident', name: t.val }; }
      if (t.type === 'SET') { eat('SET'); return { tag: 'Set' }; }
      if (t.type === 'SIZE') { eat('SIZE'); return { tag: 'Size' }; }
      if (t.type === 'INFTY') { eat('INFTY'); return { tag: 'Infty' }; }
      if (t.type === 'SUCC') { eat('SUCC'); return { tag: 'SuccMarker' }; }
      if (t.type === 'LPAREN') {
        eat('LPAREN');
        const e = parseExpr();
        eat('RPAREN');
        return e;
      }
      throw new Error(`Parse error at token "${t.val}" at line ${t.line}, col ${t.col}`);
    }

    return parseDecls();
  }

  // =========================================================================
  // 3. SCOPE CHECKER (Concrete -> Abstract)
  // =========================================================================
  function scopeCheck(cdecls) {
    const sig = new Map(); // name -> { kind: 'Con'|'Fun'|'Data'|'Let', co }
    const adecls = [];

    function addGlobal(name, info, ctx) {
      if (sig.has(name)) {
        throw new Error(`scope check error: ${ctx} -> Identifier ${name} already in signature`);
      }
      sig.set(name, info);
    }

    function checkExpr(bound, e) {
      switch (e.tag) {
        case 'Set': return { tag: 'Set' };
        case 'Size': return { tag: 'Size' };
        case 'Infty': return { tag: 'Infty' };
        case 'Succ': return { tag: 'Succ', expr: checkExpr(bound, e.expr) };
        case 'Ident': {
          if (bound.includes(e.name)) return { tag: 'Var', name: e.name };
          const g = sig.get(e.name);
          if (!g) throw new Error(`Identifier ${e.name} undefined`);
          if (g.kind === 'Con') return { tag: 'Con', co: g.co, name: e.name };
          return { tag: 'Def', name: e.name };
        }
        case 'Lam':
          return { tag: 'Lam', name: e.name, body: checkExpr([e.name, ...bound], e.body) };
        case 'Pi':
          return {
            tag: 'Pi',
            name: e.name,
            dom: checkExpr(bound, e.dom),
            cod: checkExpr([e.name, ...bound], e.cod)
          };
        case 'LLet':
          return {
            tag: 'LLet',
            name: e.name,
            ty: checkExpr(bound, e.ty),
            e1: checkExpr(bound, e.e1),
            e2: checkExpr([e.name, ...bound], e.e2)
          };
        case 'App': {
          const fn = checkExpr(bound, e.fn);
          const args = e.args.map(a => checkExpr(bound, a));
          if (fn.tag === 'App') return { tag: 'App', fn: fn.fn, args: fn.args.concat(args) };
          return { tag: 'App', fn, args };
        }
      }
    }

    function checkPattern(p, bound) {
      if (p.tag === 'IdentP') {
        const g = sig.get(p.name);
        if (p.args.length === 0) {
          if (g && g.kind === 'Con') {
            return { pat: { tag: 'ConP', co: g.co, name: p.name, args: [] }, bound };
          }
          if (bound.includes(p.name)) {
            throw new Error(`pattern not linear: ${p.name}`);
          }
          return { pat: { tag: 'VarP', name: p.name }, bound: [p.name, ...bound] };
        } else {
          if (!g || g.kind !== 'Con') {
            throw new Error(`Constructor ${p.name} undefined`);
          }
          const res = checkPatterns(p.args, bound);
          return { pat: { tag: 'ConP', co: g.co, name: p.name, args: res.pats }, bound: res.bound };
        }
      }
      if (p.tag === 'SuccP') {
        const res = checkPattern(p.pat, bound);
        return { pat: { tag: 'SuccP', pat: res.pat }, bound: res.bound };
      }
      if (p.tag === 'DotP') {
        return { pat: { tag: 'DotP', expr: p.expr }, bound };
      }
      throw new Error('Unknown pattern tag');
    }

    function checkPatterns(pats, bound) {
      const out = [];
      let cur = bound;
      for (const p of pats) {
        const r = checkPattern(p, cur);
        out.push(r.pat);
        cur = r.bound;
      }
      return { pats: out, bound: cur };
    }

    function fillDots(bound, pat) {
      if (pat.tag === 'DotP') return { tag: 'DotP', expr: checkExpr(bound, pat.expr) };
      if (pat.tag === 'SuccP') return { tag: 'SuccP', pat: fillDots(bound, pat.pat) };
      if (pat.tag === 'ConP') return { tag: 'ConP', co: pat.co, name: pat.name, args: pat.args.map(a => fillDots(bound, a)) };
      return pat;
    }

    function checkClause(expectedName, c) {
      // Like the reference implementation (Parser.y discards it; so does Mugda/Core.lean), the
      // identifier written at the start of a clause is not checked against the
      // function name; clauses belong to the enclosing `fun`/`cofun` block.
      const { pats, bound } = checkPatterns(c.pats, []);
      const pats2 = pats.map(p => fillDots(bound, p));
      const rhs = checkExpr(bound, c.rhs);
      return { pats: pats2, rhs };
    }

    function checkClauses(name, clauses) {
      if (clauses.length === 0) return [];
      const res = clauses.map(c => checkClause(name, c));
      const len0 = res[0].pats.length;
      for (const cl of res) {
        if (cl.pats.length !== len0) throw new Error(`scope check error: ${name} -> pattern length differs`);
      }
      return res;
    }

    for (const d of cdecls) {
      if (d.tag === 'DataDecl') {
        const posList = [];
        const tele = [];
        let pbound = [];
        for (const param of d.params) {
          posList.push(param.pos);
          const pty = checkExpr(pbound, param.ty);
          tele.push({ name: param.name, ty: pty });
          pbound = [param.name, ...pbound];
        }
        const ty = checkExpr(pbound, d.ts.ty);
        addGlobal(d.ts.name, { kind: 'Data' }, d.ts.name);
        const acons = [];
        for (const c of d.cons) {
          const cty = checkExpr(pbound, c.ty);
          addGlobal(c.name, { kind: 'Con', co: d.co }, c.name);
          acons.push({ name: c.name, ty: cty });
        }
        adecls.push({ tag: 'DataDecl', co: d.co, sz: d.sz, posList, tele, ts: { name: d.ts.name, ty }, cons: acons });
      } else if (d.tag === 'FunDecl') {
        const ty = checkExpr([], d.ts.ty);
        addGlobal(d.ts.name, { kind: 'Fun', co: d.co }, d.ts.name);
        const clauses = checkClauses(d.ts.name, d.clauses);
        adecls.push({ tag: 'FunDecl', co: d.co, funs: [{ ts: { name: d.ts.name, ty }, clauses }] });
      } else if (d.tag === 'MutualDecl') {
        if (d.decls.length === 0) continue;
        const co = d.decls[0].co;
        for (const sub of d.decls) {
          if (sub.tag !== 'FunDecl' || sub.co !== co) {
            throw new Error('scope check error: mutual combination not supported');
          }
        }
        const tss = [];
        for (const sub of d.decls) {
          const ty = checkExpr([], sub.ts.ty);
          addGlobal(sub.ts.name, { kind: 'Fun', co }, sub.ts.name);
          tss.push({ name: sub.ts.name, ty });
        }
        const funs = [];
        for (let i = 0; i < d.decls.length; i++) {
          const clauses = checkClauses(tss[i].name, d.decls[i].clauses);
          funs.push({ ts: tss[i], clauses });
        }
        adecls.push({ tag: 'FunDecl', co, funs });
      } else if (d.tag === 'LetDecl') {
        const ty = checkExpr([], d.ts.ty);
        const body = checkExpr([], d.body);
        addGlobal(d.ts.name, { kind: 'Let' }, d.ts.name);
        adecls.push({ tag: 'LetDecl', evalFlag: d.evalFlag, ts: { name: d.ts.name, ty }, body });
      }
    }

    return adecls;
  }

  // =========================================================================
  // 4. VALUES, EVALUATION, AND SIGNATURE
  // =========================================================================
  function vsucc(v) {
    if (v.tag === 'VInfty') return { tag: 'VInfty' };
    return { tag: 'VSucc', val: v };
  }

  function vapps(u, ws) {
    if (ws.length === 0) return u;
    if (u.tag === 'VApp') {
      return vapps(u.head, u.args.concat(ws));
    }
    if (u.tag === 'VLam') {
      const v1 = whnf(updateEnv(u.env, u.name, ws[0]), u.body);
      return vapps(v1, ws.slice(1));
    }
    if (u.tag === 'VDef') {
      return appDef(u.name, ws);
    }
    return { tag: 'VApp', head: u, args: ws };
  }

  function appDef(name, ws) {
    const entry = currentSig.get(name);
    if (entry && entry.kind === 'FunSig' && entry.co === 'Ind' && entry.enabled) {
      const m = matchClauses(entry.clauses, ws);
      if (m !== null) return m;
    }
    return { tag: 'VApp', head: { tag: 'VDef', name }, args: ws };
  }

  function updateEnv(env, name, val) {
    if (name === '') return env;
    return [{ name, val }, ...env];
  }

  function lookupEnv(env, name) {
    for (const b of env) {
      if (b.name === name) return b.val;
    }
    throw new Error(`lookup ${name} failed in env`);
  }

  let currentSig = new Map();
  let evalStepCount = 0;
  let maxEvalSteps = 2000;
  let currentMode = 'fixed';

  function whnf(env, e) {
    if (++evalStepCount > maxEvalSteps) {
      throw new Error(`Non-termination detected: exceeded ${maxEvalSteps} reduction steps!`);
    }
    switch (e.tag) {
      case 'Set': return { tag: 'VSet' };
      case 'Size': return { tag: 'VSize' };
      case 'Infty': return { tag: 'VInfty' };
      case 'Succ': return vsucc(whnf(env, e.expr));
      case 'Var': return lookupEnv(env, e.name);
      case 'Con': return { tag: 'VCon', co: e.co, name: e.name };
      case 'Def': {
        const entry = currentSig.get(e.name);
        if (entry && entry.kind === 'LetSig') return entry.val;
        return { tag: 'VDef', name: e.name };
      }
      case 'Lam': return { tag: 'VLam', name: e.name, env, body: e.body };
      case 'Pi': return { tag: 'VPi', name: e.name, dom: whnf(env, e.dom), env, cod: e.cod };
      case 'LLet': {
        const v1 = whnf(env, e.e1);
        return whnf(updateEnv(env, e.name, v1), e.e2);
      }
      case 'App': {
        const u = whnf(env, e.fn);
        const ws = e.args.map(a => whnf(env, a));
        return vapps(u, ws);
      }
    }
  }

  function matchPat(env, p, v0) {
    const v = (p.tag === 'ConP' && p.co === 'CoInd') ? force(v0) : v0;
    if (p.tag === 'DotP') return { status: 'matched', env };
    if (p.tag === 'VarP') return { status: 'matched', env: updateEnv(env, p.name, v) };
    if (p.tag === 'SuccP') {
      if (v.tag === 'VSucc') return matchPat(env, p.pat, v.val);
      if (v.tag === 'VInfty') return matchPat(env, p.pat, { tag: 'VInfty' });
      return { status: 'stuck' };
    }
    if (p.tag === 'ConP') {
      if (v.tag === 'VCon') {
        if (v.name !== p.name) return { status: 'mismatch' };
        return p.args.length === 0 ? { status: 'matched', env } : { status: 'stuck' };
      }
      if (v.tag === 'VApp' && v.head.tag === 'VCon') {
        if (v.head.name !== p.name) return { status: 'mismatch' };
        return matchPats(env, p.args, v.args);
      }
      return { status: 'stuck' };
    }
    return { status: 'stuck' };
  }

  function matchPats(env, pats, vals) {
    if (pats.length !== vals.length) return { status: 'stuck' };
    let cur = env;
    for (let i = 0; i < pats.length; i++) {
      const r = matchPat(cur, pats[i], vals[i]);
      if (r.status !== 'matched') return r;
      cur = r.env;
    }
    return { status: 'matched', env: cur };
  }

  function matchClauses(clauses, vals) {
    for (const cl of clauses) {
      if (vals.length < cl.pats.length) return null;
      const used = vals.slice(0, cl.pats.length);
      const rest = vals.slice(cl.pats.length);
      const r = matchPats([], cl.pats, used);
      if (r.status === 'matched') {
        const rhsVal = whnf(r.env, cl.rhs);
        return vapps(rhsVal, rest);
      }
      if (r.status === 'stuck' && currentMode !== '2008') {
        return null;
      }
    }
    return null;
  }

  function force(v) {
    if (v.tag === 'VDef') {
      const entry = currentSig.get(v.name);
      if (entry && entry.kind === 'FunSig' && entry.co === 'CoInd' && entry.enabled) {
        const r = matchClauses(entry.clauses, []);
        return r !== null ? force(r) : v;
      }
      return v;
    }
    if (v.tag === 'VApp' && v.head.tag === 'VDef') {
      const entry = currentSig.get(v.head.name);
      if (entry && entry.kind === 'FunSig' && entry.co === 'CoInd' && entry.enabled) {
        const r = matchClauses(entry.clauses, v.args);
        return r !== null ? force(r) : v;
      }
      return v;
    }
    return v;
  }

  function nfVal(v) {
    const vf = force(v);
    if (vf.tag === 'VApp') {
      return { tag: 'VApp', head: nfVal(vf.head), args: vf.args.map(nfVal) };
    }
    if (vf.tag === 'VSucc') {
      return vsucc(nfVal(vf.val));
    }
    return vf;
  }

  function showVal(v) {
    switch (v.tag) {
      case 'VSet': return 'Set';
      case 'VSize': return 'Size';
      case 'VInfty': return '#';
      case 'VSucc': return `($ ${showVal(v.val)})`;
      case 'VGen': return `${v.k}`;
      case 'VCon': return v.name;
      case 'VDef': return v.name;
      case 'VApp': return `(${showVal(v.head)} ${v.args.map(showVal).join(' ')})`;
      case 'VPi': return `(${v.name} : ${showVal(v.dom)}) -> ...`;
      case 'VLam': return `\\${v.name} -> ...`;
      default: return JSON.stringify(v);
    }
  }

  function valEqualSyntactic(v1, v2) {
    if (v1.tag !== v2.tag) return false;
    switch (v1.tag) {
      case 'VSet':
      case 'VSize':
      case 'VInfty':
        return true;
      case 'VGen':
        return v1.k === v2.k;
      case 'VCon':
      case 'VDef':
        return v1.name === v2.name;
      case 'VSucc':
        return valEqualSyntactic(v1.val, v2.val);
      case 'VApp':
        return valEqualSyntactic(v1.head, v2.head) &&
          v1.args.length === v2.args.length &&
          v1.args.every((a, i) => valEqualSyntactic(a, v2.args[i]));
      default:
        return false;
    }
  }

  // Substitution on values
  function substVal(subst, v) {
    switch (v.tag) {
      case 'VGen': {
        const found = subst.get(v.k);
        return found !== undefined ? found : v;
      }
      case 'VSucc':
        return vsucc(substVal(subst, v.val));
      case 'VApp': {
        const h = substVal(subst, v.head);
        const as = v.args.map(a => substVal(subst, a));
        return vapps(h, as);
      }
      case 'VPi':
        return {
          tag: 'VPi',
          name: v.name,
          dom: substVal(subst, v.dom),
          env: substEnv(subst, v.env),
          cod: v.cod
        };
      case 'VLam':
        return {
          tag: 'VLam',
          name: v.name,
          env: substEnv(subst, v.env),
          body: v.body
        };
      default:
        return v;
    }
  }

  function substEnv(subst, env) {
    return env.map(b => ({ name: b.name, val: substVal(subst, b.val) }));
  }

  function compSubst(s1, s2) {
    const out = new Map();
    for (const [k, v] of s1.entries()) {
      out.set(k, substVal(s2, v));
    }
    for (const [k, v] of s2.entries()) {
      if (!out.has(k)) out.set(k, v);
    }
    return out;
  }

  // =========================================================================
  // 5. OCCURS CHECK (nocc) & STRICT POSITIVITY (SPos)
  // =========================================================================
  function nocc(k, target, v) {
    // No forcing here: like SPos.hs / Mugda/Core.lean `nocc`, the occurs check
    // inspects the value as is (forcing could unfold a coinductive value forever).
    const vf = v;
    if (valEqualSyntactic(target, vf)) return false;
    switch (vf.tag) {
      case 'VSucc':
        return nocc(k, target, vf.val);
      case 'VApp':
        return nocc(k, target, vf.head) && vf.args.every(a => nocc(k, target, a));
      case 'VPi': {
        if (!nocc(k, target, vf.dom)) return false;
        const codVal = whnf(updateEnv(vf.env, vf.name, { tag: 'VGen', k }), vf.cod);
        return nocc(k + 1, target, codVal);
      }
      case 'VLam': {
        const bodyVal = whnf(updateEnv(vf.env, vf.name, { tag: 'VGen', k }), vf.body);
        return nocc(k + 1, target, bodyVal);
      }
      default:
        return true;
    }
  }

  function spos(k, target, v) {
    const vf = v; // no forcing, cf. Mugda/Core.lean `spos`
    if (valEqualSyntactic(vf, target)) return true;
    if (vf.tag === 'VPi') {
      if (!nocc(k, target, vf.dom)) return false;
      const codVal = whnf(updateEnv(vf.env, vf.name, { tag: 'VGen', k }), vf.cod);
      return spos(k + 1, target, codVal);
    }
    if (vf.tag === 'VLam') {
      const bodyVal = whnf(updateEnv(vf.env, vf.name, { tag: 'VGen', k }), vf.body);
      return spos(k + 1, target, bodyVal);
    }
    if (vf.tag === 'VSucc') {
      return spos(k, target, vf.val);
    }
    if (vf.tag === 'VApp' && vf.head.tag === 'VDef') {
      const entry = currentSig.get(vf.head.name);
      if (entry && entry.kind === 'DataSig') {
        const posList = entry.posList;
        for (let i = 0; i < vf.args.length; i++) {
          const isSPos = i < posList.length && posList[i] === 'SPos';
          if (isSPos) {
            if (!spos(k, target, vf.args[i])) return false;
          } else {
            if (!nocc(k, target, vf.args[i])) return false;
          }
        }
        return true;
      }
    }
    return nocc(k, target, vf);
  }

  function sposConstructor(dname, k, posList, v, mode) {
    if (v.tag === 'VPi') {
      const kArg = mode === 'fixed' ? k : 0; // Bug 6: SPos.hs passed 0 instead of k
      if (!spos(kArg, { tag: 'VDef', name: dname }, v.dom)) {
        throw new Error('rec. arg not strictly positive');
      }
      if (k >= posList.length) {
        for (let idx = 0; idx < posList.length; idx++) {
          if (posList[idx] === 'SPos') {
            if (!spos(kArg, { tag: 'VGen', k: idx }, v.dom)) {
              throw new Error(`param not strictly positive: ${idx}`);
            }
          }
        }
      }
      const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
      sposConstructor(dname, k + 1, posList, bv, mode);
    }
  }

  // =========================================================================
  // 6. COMPLETENESS OF SIZE PATTERNS
  // =========================================================================
  function completePatterns(clauses, mode) {
    if (mode === '2008') {
      // Bug 5: Completness.hs in 2008 had `completeFun _ = True`
      return true;
    }
    function cp(p) {
      if (p.tag === 'SuccP') return false;
      if (p.tag === 'ConP') return p.args.every(cp);
      return true;
    }
    return clauses.every(cl => cl.pats.every(cp));
  }

  // =========================================================================
  // 7. SIZE-CHANGE TERMINATION CHECKER
  // =========================================================================
  function exprToPattern(e) {
    switch (e.tag) {
      case 'Var': return { tag: 'VarP', name: e.name };
      case 'Con': return { tag: 'ConP', co: e.co, name: e.name, args: [] };
      case 'Succ': return { tag: 'SuccP', pat: exprToPattern(e.expr) };
      case 'App': {
        if (e.fn.tag === 'Con') {
          return { tag: 'ConP', co: e.fn.co, name: e.fn.name, args: e.args.map(exprToPattern) };
        }
        return { tag: 'DotP', expr: e };
      }
      default:
        return { tag: 'DotP', expr: e };
    }
  }

  function exprEqualSyntactic(e1, e2) {
    return JSON.stringify(e1) === JSON.stringify(e2);
  }

  function isPureConP(p) {
    if (p.tag === 'VarP') return true;
    if (p.tag === 'ConP') return p.args.every(isPureConP);
    return false;
  }

  function diag(m) {
    const n = Math.min(m.length, m[0] ? m[0].length : 0);
    const out = [];
    for (let i = 0; i < n; i++) out.push(m[i][i]);
    return out;
  }

  function transpose(m) {
    if (m.length === 0) return [];
    return m[0].map((_, c) => m.map(r => r[c]));
  }

  function collapse(mOrObj, mode) {
    const m = Array.isArray(mOrObj) ? mOrObj : mOrObj.m;
    return minL(diag(m), mode);
  }

  function maxO(o1, o2, mode) {
    if (o1.tag === 'Lt' || o2.tag === 'Lt') return { tag: 'Lt' };
    if (o1.tag === 'Un') return o2;
    if (o2.tag === 'Un') return o1;
    if (o1.tag === 'Eq' && o2.tag === 'Eq') return { tag: 'Eq' };
    if (o1.tag === 'Mat' && o2.tag === 'Eq') return maxO(collapse(o1, mode), { tag: 'Eq' }, mode);
    if (o1.tag === 'Eq' && o2.tag === 'Mat') return maxO({ tag: 'Eq' }, collapse(o2, mode), mode);
    if (o1.tag === 'Mat' && o2.tag === 'Mat') {
      if (mode === '2008' && o1.m.length === o2.m.length && o1.m[0].length === o2.m[0].length) {
        // Bug 3b: entrywise maxO on Mat in 2008
        return {
          tag: 'Mat',
          m: o1.m.map((row, i) => row.map((cell, j) => maxO(cell, o2.m[i][j], mode)))
        };
      }
      return maxO(collapse(o1, mode), collapse(o2, mode), mode);
    }
    return { tag: 'Un' };
  }

  function minO(o1, o2, mode) {
    if (o1.tag === 'Un' || o2.tag === 'Un') return { tag: 'Un' };
    if (o1.tag === 'Lt') return o2;
    if (o2.tag === 'Lt') return o1;
    if (o1.tag === 'Eq' && o2.tag === 'Eq') return { tag: 'Eq' };
    if (o1.tag === 'Mat' && o2.tag === 'Eq') return minO(collapse(o1, mode), { tag: 'Eq' }, mode);
    if (o1.tag === 'Eq' && o2.tag === 'Mat') return minO({ tag: 'Eq' }, collapse(o2, mode), mode);
    if (o1.tag === 'Mat' && o2.tag === 'Mat') {
      if (o1.m.length === o2.m.length && o1.m[0].length === o2.m[0].length) {
        return {
          tag: 'Mat',
          m: o1.m.map((row, i) => row.map((cell, j) => minO(cell, o2.m[i][j], mode)))
        };
      }
      return minO(collapse(o1, mode), collapse(o2, mode), mode);
    }
    return { tag: 'Un' };
  }

  function multO(o1, o2, mode) {
    if (o1.tag === 'Un' || o2.tag === 'Un') return { tag: 'Un' };
    if (o1.tag === 'Eq') return o2;
    if (o2.tag === 'Eq') return o1;
    if (o1.tag === 'Lt' && o2.tag === 'Lt') return { tag: 'Lt' };
    if (o1.tag === 'Lt' && o2.tag === 'Mat') return multO({ tag: 'Lt' }, collapse(o2, mode), mode);
    if (o1.tag === 'Mat' && o2.tag === 'Lt') return multO(collapse(o1, mode), { tag: 'Lt' }, mode);
    if (o1.tag === 'Mat' && o2.tag === 'Mat') {
      if (o1.m[0].length === o2.m.length) {
        return { tag: 'Mat', m: multMat(o1.m, o2.m, mode) };
      }
      return multO(collapse(o1, mode), collapse(o2, mode), mode);
    }
    return { tag: 'Un' };
  }

  function maxL(list, mode) {
    if (list.length === 0) return { tag: 'Un' };
    return list.slice(1).reduce((acc, x) => maxO(acc, x, mode), list[0]);
  }

  function minL(list, mode) {
    if (list.length === 0) return { tag: 'Un' };
    return list.slice(1).reduce((acc, x) => minO(acc, x, mode), list[0]);
  }

  function multMat(m1, m2, mode) {
    const m2T = transpose(m2);
    return m1.map(r => m2T.map(c => maxL(r.map((x, i) => multO(x, c[i], mode)), mode)));
  }

  function subterm(p, vname, mode) {
    if (p.tag === 'VarP') {
      return p.name === vname ? { tag: 'Eq' } : { tag: 'Un' };
    }
    if (p.tag === 'SuccP') {
      return multO({ tag: 'Lt' }, subterm(p.pat, vname, mode), mode);
    }
    if (p.tag === 'ConP' && p.co === 'Ind') {
      return multO({ tag: 'Lt' }, maxL(p.args.map(a => subterm(a, vname, mode)), mode), mode);
    }
    if (p.tag === 'DotP') {
      const ep = exprToPattern(p.expr);
      if (ep.tag !== 'DotP') return subterm(ep, vname, mode);
      return { tag: 'Un' };
    }
    return { tag: 'Un' };
  }

  function comparePattern(e, p, mode) {
    if (p.tag === 'DotP') {
      const ep = exprToPattern(p.expr);
      if (ep.tag !== 'DotP') return comparePattern(e, ep, mode);
      if (exprEqualSyntactic(e, p.expr)) return { tag: 'Eq' };
      return { tag: 'Un' };
    }
    if (e.tag === 'Var') return subterm(p, e.name, mode);
    if (e.tag === 'App' && e.fn.tag === 'Var') return subterm(p, e.fn.name, mode);
    if (e.tag === 'Con' && p.tag === 'ConP' && e.name === p.name && p.args.length === 0) {
      return { tag: 'Eq' };
    }
    if (e.tag === 'Succ' && p.tag === 'SuccP') {
      return comparePattern(e.expr, p.pat, mode);
    }
    if (e.tag === 'App' && e.fn.tag === 'Con' && p.tag === 'ConP' && e.fn.name === p.name && e.args.length === p.args.length) {
      if (e.args.length === 1) {
        return comparePattern(e.args[0], p.args[0], mode);
      }
      // Bug 3a: In 2008 mode, Mat was created for ALL constructors of arity >= 2 (including sized/dot patterns).
      // In fixed mode, Mat is only created when all subpatterns are pure structural patterns (no DotP or SuccP).
      if (mode === '2008' || p.args.every(isPureConP)) {
        return {
          tag: 'Mat',
          m: p.args.map(pi => e.args.map(ej => comparePattern(ej, pi, mode)))
        };
      }
      return minL(e.args.map((ej, i) => comparePattern(ej, p.args[i], mode)), mode);
    }
    return { tag: 'Un' };
  }

  function collectCalls(fnames, clause, callerName, callerArity, mode) {
    const pats = clause.pats;
    const calls = [];

    function extract(e) {
      if (e.tag === 'Def' && fnames.has(e.name)) {
        calls.push(buildCallMatrix(callerName, pats, e.name, [], fnames.get(e.name), mode));
        return;
      }
      if (e.tag === 'App') {
        if (e.fn.tag === 'Def' && fnames.has(e.fn.name)) {
          calls.push(buildCallMatrix(callerName, pats, e.fn.name, e.args, fnames.get(e.fn.name), mode));
          e.args.forEach(extract);
          return;
        }
        extract(e.fn);
        e.args.forEach(extract);
        return;
      }
      if (e.tag === 'Succ') { extract(e.expr); return; }
      if (e.tag === 'Lam') { extract(e.body); return; }
      if (e.tag === 'Pi') { extract(e.dom); extract(e.cod); return; }
      if (e.tag === 'LLet') {
        if (mode === '2008') {
          // Bug 4: Termination.hs line 307 matched (LLet _ e1 t1 e2 -> collect e1 ++ collect e2),
          // where the first Expr field is `ty` and the second is `e1`!
          extract(e.ty);
          extract(e.e2);
        } else {
          extract(e.ty);
          extract(e.e1);
          extract(e.e2);
        }
      }
    }

    extract(clause.rhs);
    return calls;
  }

  function buildCallMatrix(caller, pats, callee, args, calleeArity, mode) {
    const padded = args.slice(0, calleeArity);
    const m = pats.map(pi => {
      const row = [];
      for (let j = 0; j < calleeArity; j++) {
        if (j < padded.length) row.push(comparePattern(padded[j], pi, mode));
        else row.push({ tag: 'Un' });
      }
      return row;
    });
    return { caller, callee, m };
  }

  function showOrder(o) {
    if (o.tag === 'Lt') return '<';
    if (o.tag === 'Eq') return '<=';
    if (o.tag === 'Un') return '?';
    if (o.tag === 'Mat') {
      return '[' + o.m.map(r => r.map(showOrder).join(' ')).join('; ') + ']';
    }
    return '?';
  }

  function callKey(c) {
    return `${c.caller}->${c.callee}:${ JSON.stringify(c.m) }`;
  }

  function isDecr(o) {
    if (o.tag === 'Lt') return true;
    if (o.tag === 'Mat') return diag(o.m).some(isDecr);
    return false;
  }

  function terminationCheck(funs, mode) {
    const fnames = new Map();
    for (const f of funs) {
      const arity = f.clauses.length > 0 ? f.clauses[0].pats.length : 0;
      fnames.set(f.ts.name, arity);
    }
    const initialCalls = [];
    const callMap = new Map();
    for (const f of funs) {
      const arity = fnames.get(f.ts.name);
      for (const cl of f.clauses) {
        const cs = collectCalls(fnames, cl, f.ts.name, arity, mode);
        for (const c of cs) {
          const k = callKey(c);
          if (!callMap.has(k)) {
            callMap.set(k, c);
            initialCalls.push(c);
          }
        }
      }
    }

    // Complete call graph under composition
    let changed = true;
    while (changed) {
      changed = false;
      const current = Array.from(callMap.values());
      for (const c1 of current) {
        for (const c2 of current) {
          if (c1.callee === c2.caller && c1.m.length > 0 && c2.m.length > 0) {
            const m = multMat(c1.m, c2.m, mode);
            const comp = { caller: c1.caller, callee: c2.callee, m };
            const k = callKey(comp);
            if (!callMap.has(k)) {
              callMap.set(k, comp);
              changed = true;
            }
          }
        }
      }
    }

    const failed = [];
    for (const f of funs) {
      const name = f.ts.name;
      let ok = true;
      for (const c of callMap.values()) {
        if (c.caller === name && c.callee === name) {
          const sq = multMat(c.m, c.m, mode);
          if (JSON.stringify(sq) === JSON.stringify(c.m)) {
            // Idempotent
            if (!diag(c.m).some(isDecr)) {
              ok = false;
              break;
            }
          }
        }
      }
      if (!ok) failed.push(name);
    }

    return { ok: failed.length === 0, failed, initialCalls };
  }

  // =========================================================================
  // 8. TYPE CHECKER & ADMISSIBILITY
  // =========================================================================
  function switchForce(f) {
    if (f === 'L') return 'R';
    if (f === 'R') return 'L';
    return 'N';
  }

  function eqVal(k, u1, u2, f = 'N') {
    const u1f = force(u1);
    const u2f = force(u2);
    const c1 = !valEqualSyntactic(u1f, u1);
    const c2 = !valEqualSyntactic(u2f, u2);
    if (c1 && !c2 && f !== 'R') return eqVal(k, u1f, u2, 'L');
    if (!c1 && c2 && f !== 'L') return eqVal(k, u1, u2f, 'R');
    const a = u1;
    const b = u2;
    if (a.tag === 'VSucc' && b.tag === 'VSucc') return eqVal(k, a.val, b.val, f);
    if (a.tag === 'VApp' && b.tag === 'VApp') {
      eqVal(k, a.head, b.head, f);
      if (a.args.length !== b.args.length) throw new Error('mismatch number of arguments');
      for (let i = 0; i < a.args.length; i++) eqVal(k, a.args[i], b.args[i], f);
      return;
    }
    if (a.tag === 'VPi' && b.tag === 'VPi') {
      eqVal(k, a.dom, b.dom, f);
      const v1 = whnf(updateEnv(a.env, a.name, { tag: 'VGen', k }), a.cod);
      const v2 = whnf(updateEnv(b.env, b.name, { tag: 'VGen', k }), b.cod);
      return eqVal(k + 1, v1, v2, f);
    }
    if (a.tag === 'VLam' && b.tag === 'VLam') {
      const v1 = whnf(updateEnv(a.env, a.name, { tag: 'VGen', k }), a.body);
      const v2 = whnf(updateEnv(b.env, b.name, { tag: 'VGen', k }), b.body);
      return eqVal(k + 1, v1, v2, f);
    }
    if (valEqualSyntactic(a, b)) return;
    throw new Error(`eqVal error ${f} ${showVal(u1)} @@ ${showVal(u2)}`);
  }

  function leqSize(u1, u2) {
    if (u2.tag === 'VInfty') return;
    if (u1.tag === 'VGen' && u2.tag === 'VGen' && u1.k === u2.k) return;
    if (u1.tag === 'VSucc' && u2.tag === 'VSucc') return leqSize(u1.val, u2.val);
    if (u2.tag === 'VSucc') return leqSize(u1, u2.val);
    throw new Error(`size mismatch: ${showVal(u1)} <= ${showVal(u2)}`);
  }

  function leqVal(k, u1, u2, f = 'N') {
    const u1f = force(u1);
    const u2f = force(u2);
    const c1 = !valEqualSyntactic(u1f, u1);
    const c2 = !valEqualSyntactic(u2f, u2);
    if (c1 && !c2 && f !== 'R') return leqVal(k, u1f, u2, 'L');
    if (!c1 && c2 && f !== 'L') return leqVal(k, u1, u2f, 'R');
    const a = u1;
    const b = u2;
    if (a.tag === 'VSucc' && b.tag === 'VSucc') return leqVal(k, a.val, b.val, f);
    if (a.tag === 'VApp' && b.tag === 'VApp' && a.head.tag === 'VDef' && b.head.tag === 'VDef' && a.head.name === b.head.name) {
      const entry = currentSig.get(a.head.name);
      if (entry && entry.kind === 'DataSig') {
        if (a.args.length !== b.args.length) throw new Error('leqVal argument length mismatch');
        const p = entry.posList.length;
        for (let i = 0; i < a.args.length; i++) {
          if (i < p) {
            if (entry.posList[i] === 'SPos') leqVal(k, a.args[i], b.args[i], f);
            else eqVal(k, a.args[i], b.args[i], f);
          } else if (i === p && entry.sz === 'Sized') {
            if (entry.co === 'Ind') leqSize(a.args[i], b.args[i]);
            else leqSize(b.args[i], a.args[i]);
          } else {
            eqVal(k, a.args[i], b.args[i], f);
          }
        }
        return;
      }
    }
    if (a.tag === 'VApp' && b.tag === 'VApp') {
      leqVal(k, a.head, b.head, f);
      if (a.args.length !== b.args.length) throw new Error('mismatch number of arguments');
      for (let i = 0; i < a.args.length; i++) eqVal(k, a.args[i], b.args[i], f);
      return;
    }
    if (a.tag === 'VPi' && b.tag === 'VPi') {
      leqVal(k, b.dom, a.dom, switchForce(f));
      const v1 = whnf(updateEnv(a.env, a.name, { tag: 'VGen', k }), a.cod);
      const v2 = whnf(updateEnv(b.env, b.name, { tag: 'VGen', k }), b.cod);
      return leqVal(k + 1, v1, v2, f);
    }
    if (a.tag === 'VLam' && b.tag === 'VLam') {
      const v1 = whnf(updateEnv(a.env, a.name, { tag: 'VGen', k }), a.body);
      const v2 = whnf(updateEnv(b.env, b.name, { tag: 'VGen', k }), b.body);
      return leqVal(k + 1, v1, v2, f);
    }
    if (valEqualSyntactic(a, b)) return;
    throw new Error(`leqVal error: ${showVal(u1)} @@ ${showVal(u2)}`);
  }

  function runProgram(source, options = {}) {
    const mode = options.mode || 'fixed';
    currentMode = mode;
    maxEvalSteps = options.maxEvalSteps || 15000;
    evalStepCount = 0;
    currentSig = new Map();
    const output = [];
    const diagnostics = [];
    const callMatrices = [];

    output.push(`***** Mugda v1.0 (${mode === 'fixed' ? 'Bug-Fixed' : 'Original 2008'}) *****`);
    output.push('--- scope checking ---');
    const cdecls = parse(source);
    const adecls = scopeCheck(cdecls);

    output.push('--- type checking ---');

    function teleToType(tele, t) {
      let res = t;
      for (let i = tele.length - 1; i >= 0; i--) {
        res = { tag: 'Pi', name: tele[i].name, dom: tele[i].ty, cod: res };
      }
      return res;
    }

    function typeToTele(t) {
      const tele = [];
      let cur = t;
      while (cur.tag === 'Pi') {
        tele.push({ name: cur.name, ty: cur.dom });
        cur = cur.cod;
      }
      return { tele, target: cur };
    }

    function checkType(k, rho, gamma, e) {
      if (e.tag === 'Set') return;
      if (e.tag === 'Size') return;
      if (e.tag === 'Pi') {
        checkType(k, rho, gamma, e.dom);
        const vdom = whnf(rho, e.dom);
        checkType(k + 1, updateEnv(rho, e.name, { tag: 'VGen', k }), updateEnv(gamma, e.name, vdom), e.cod);
        return;
      }
      checkSType(k, rho, gamma, e);
    }

    function checkSType(k, rho, gamma, e) {
      checkExpr(k, rho, gamma, e, { tag: 'VSet' });
    }

    function checkExpr(k, rho, gamma, e, tv) {
      const tvf = force(tv);
      if (e.tag === 'Lam') {
        if (tvf.tag !== 'VPi') throw new Error('expected Pi type for lambda');
        const bv = whnf(updateEnv(tvf.env, tvf.name, { tag: 'VGen', k }), tvf.cod);
        checkExpr(k + 1, updateEnv(rho, e.name, { tag: 'VGen', k }), updateEnv(gamma, e.name, tvf.dom), e.body, bv);
        return;
      }
      if (e.tag === 'Succ') {
        eqVal(k, tvf, { tag: 'VSize' });
        checkExpr(k, rho, gamma, e.expr, { tag: 'VSize' });
        return;
      }
      if (e.tag === 'Pi') {
        eqVal(k, tvf, { tag: 'VSet' });
        checkSType(k, rho, gamma, e.dom);
        const vdom = whnf(rho, e.dom);
        checkSType(k + 1, updateEnv(rho, e.name, { tag: 'VGen', k }), updateEnv(gamma, e.name, vdom), e.cod);
        return;
      }
      if (e.tag === 'LLet') {
        checkType(k, rho, gamma, e.ty);
        const vt = whnf(rho, e.ty);
        checkExpr(k, rho, gamma, e.e1, vt);
        const v1 = whnf(rho, e.e1);
        checkExpr(k, updateEnv(rho, e.name, v1), updateEnv(gamma, e.name, vt), e.e2, tvf);
        return;
      }
      const tv2 = inferExpr(k, rho, gamma, e);
      leqVal(k, tv2, tvf);
    }

    function inferExpr(k, rho, gamma, e) {
      switch (e.tag) {
        case 'Infty': return { tag: 'VSize' };
        case 'Var': return lookupEnv(gamma, e.name);
        case 'Con':
        case 'Def': {
          const entry = currentSig.get(e.name);
          if (!entry) throw new Error(`Undefined ${e.name}`);
          return entry.ty;
        }
        case 'App': {
          let tv = inferExpr(k, rho, gamma, e.fn);
          for (const arg of e.args) {
            const tvf = force(tv);
            if (tvf.tag !== 'VPi') throw new Error(`expected Pi type in application, got ${showVal(tvf)}`);
            checkExpr(k, rho, gamma, arg, tvf.dom);
            const varg = whnf(rho, arg);
            tv = whnf(updateEnv(tvf.env, tvf.name, varg), tvf.cod);
          }
          return tv;
        }
        default:
          throw new Error(`not a set: ${e.tag}`);
      }
    }

    function checkDataType(k, rho, gamma, p, e) {
      if (e.tag === 'Pi') {
        if (k < p) checkType(k, rho, gamma, e.dom);
        else checkSType(k, rho, gamma, e.dom);
        const vdom = whnf(rho, e.dom);
        checkDataType(k + 1, updateEnv(rho, e.name, { tag: 'VGen', k }), updateEnv(gamma, e.name, vdom), p, e.cod);
        return;
      }
      if (e.tag === 'Set') return;
      throw new Error("doesn't target Set");
    }

    function checkConType(k, rho, gamma, p, e) {
      if (e.tag === 'Pi') {
        if (k >= p) checkSType(k, rho, gamma, e.dom);
        const vdom = whnf(rho, e.dom);
        checkConType(k + 1, updateEnv(rho, e.name, { tag: 'VGen', k }), updateEnv(gamma, e.name, vdom), p, e.cod);
        return;
      }
      checkSType(k, rho, gamma, e);
    }

    function szConstructor(dname, p, vt) {
      let cur = vt;
      for (let i = 0; i < p; i++) {
        cur = whnf(updateEnv(cur.env, cur.name, { tag: 'VGen', k: i }), cur.cod);
      }
      if (cur.tag !== 'VPi' || cur.dom.tag !== 'VSize') {
        throw new Error('constructor of sized data misses size');
      }
      const next = whnf(updateEnv(cur.env, cur.name, { tag: 'VGen', k: p }), cur.cod);
      szConArgs(p + 1, dname, p, p, next);
    }

    function szConArgs(k, dname, p, szVar, v) {
      if (v.tag === 'VPi') {
        szArg(k, dname, p, szVar, v.dom);
        const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
        szConArgs(k + 1, dname, p, szVar, bv);
        return;
      }
      if (v.tag === 'VApp' && v.head.tag === 'VDef' && v.head.name === dname) {
        const rargs = v.args.slice(0, p).concat(v.args.slice(p + 1));
        const b = rargs.every(a => nocc(k, { tag: 'VGen', k: szVar }, a));
        if (!b) throw new Error('szTarget: bad size index in target');
        eqVal(k, v.args[p], { tag: 'VSucc', val: { tag: 'VGen', k: szVar } });
        return;
      }
      throw new Error('szTarget error');
    }

    function szArg(k, dname, p, i, v) {
      if (v.tag === 'VApp' && v.head.tag === 'VDef' && v.head.name === dname) {
        const rargs = v.args.slice(0, p).concat(v.args.slice(p + 1));
        if (!rargs.every(a => nocc(k, { tag: 'VGen', k: i }, a))) {
          throw new Error('szData: size occurs in non-size index');
        }
        eqVal(k, v.args[p], { tag: 'VGen', k: i });
        return;
      }
      if (v.tag === 'VApp') {
        if (v.head.tag === 'VGen' && v.head.k === i) throw new Error('szArg error');
        for (const a of v.args) szArg(k, dname, p, i, a);
        return;
      }
      if (v.tag === 'VSucc') {
        szArg(k, dname, p, i, v.val);
        return;
      }
      if (v.tag === 'VPi') {
        szArg(k, dname, p, i, v.dom);
        const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
        szArg(k + 1, dname, p, i, bv);
        return;
      }
      if (v.tag === 'VGen' && v.k === i) throw new Error('szArg: bare size var');
    }

    // Admissibility checks
    function isSizedDataApp(k, i, v, expectedCo, checkParams) {
      const vf = force(v);
      if (vf.tag === 'VApp' && vf.head.tag === 'VDef') {
        const entry = currentSig.get(vf.head.name);
        if (entry && entry.kind === 'DataSig' && entry.co === expectedCo && entry.sz === 'Sized') {
          const p = entry.posList.length;
          if (vf.args[p] && vf.args[p].tag === 'VGen' && vf.args[p].k === i) {
            if (checkParams || mode === 'fixed') {
              // Bug 2: In 2008 mode, szSizeVarTarget and szUsed' omitted the parameter nocc check!
              const rargs = vf.args.slice(0, p).concat(vf.args.slice(p + 1));
              return rargs.every(arg => nocc(k, { tag: 'VGen', k: i }, arg));
            }
            return true;
          }
        }
      }
      return false;
    }

    function szUsed(k, i, used, v) {
      if (v.tag === 'VPi') {
        const b1 = isSizedDataApp(k, i, v.dom, 'Ind', false);
        const b2 = nocc(k, { tag: 'VGen', k: i }, v.dom);
        if (!(b1 || b2)) return false;
        const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
        return szUsed(k + 1, i, used || b1, bv);
      }
      if (!used) return true;
      try {
        const subst = new Map([[i, { tag: 'VSucc', val: { tag: 'VGen', k: i } }]]);
        const v2 = substVal(subst, v);
        leqVal(k, v, v2);
        return true;
      } catch (_) {
        return false;
      }
    }

    function szCheckIndFun(k, v) {
      if (v.tag === 'VPi') {
        const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
        if (v.dom.tag === 'VSize') {
          return szUsed(k + 1, k, false, bv) && szCheckIndFun(k + 1, bv);
        }
        return szCheckIndFun(k + 1, bv);
      }
      return true;
    }

    function szSizeVarCo(k, i, v) {
      if (v.tag === 'VPi') {
        if (!nocc(k, { tag: 'VGen', k: i }, v.dom)) return false;
        const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
        return szSizeVarCo(k + 1, i, bv);
      }
      return isSizedDataApp(k, i, v, 'CoInd', false);
    }

    function szCheckCoFun(k, v) {
      if (v.tag === 'VPi') {
        const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
        if (v.dom.tag === 'VSize') {
          return szSizeVarCo(k + 1, k, bv) && szCheckCoFun(k + 1, bv);
        }
        return szCheckCoFun(k + 1, bv);
      }
      return true;
    }

    // Pattern checking & Unification
    function p2v(k, p) {
      if (p.tag === 'VarP') return { val: { tag: 'VGen', k }, k: k + 1 };
      if (p.tag === 'DotP') return { val: { tag: 'VGen', k }, k: k + 1 };
      if (p.tag === 'SuccP') {
        const r = p2v(k, p.pat);
        return { val: { tag: 'VSucc', val: r.val }, k: r.k };
      }
      if (p.tag === 'ConP') {
        if (p.args.length === 0) return { val: { tag: 'VCon', co: p.co, name: p.name }, k };
        let curK = k;
        const vals = [];
        for (const a of p.args) {
          const r = p2v(curK, a);
          vals.push(r.val);
          curK = r.k;
        }
        return { val: { tag: 'VApp', head: { tag: 'VCon', co: p.co, name: p.name }, args: vals }, k: curK };
      }
    }

    function inst(m, flexSet, v1, v2) {
      if (v1.tag === 'VGen' && v2.tag === 'VGen' && v1.k === v2.k) return new Map();
      if (v1.tag === 'VGen' && flexSet.has(v1.k)) {
        if (!nocc(m, v1, v2)) throw new Error('occurs check failed');
        return new Map([[v1.k, v2]]);
      }
      if (v2.tag === 'VGen' && flexSet.has(v2.k)) {
        if (!nocc(m, v2, v1)) throw new Error('occurs check failed');
        return new Map([[v2.k, v1]]);
      }
      if (v1.tag === 'VSucc' && v2.tag === 'VSucc') return inst(m, flexSet, v1.val, v2.val);
      if (v1.tag === 'VSucc' && v2.tag === 'VInfty') return inst(m, flexSet, v1.val, { tag: 'VInfty' });
      if (v1.tag === 'VApp' && v2.tag === 'VApp') {
        if (
          (v1.head.tag === 'VDef' && v2.head.tag === 'VDef' && v1.head.name === v2.head.name) ||
          (v1.head.tag === 'VCon' && v2.head.tag === 'VCon' && v1.head.name === v2.head.name)
        ) {
          return instList(m, flexSet, v1.args, v2.args);
        }
      }
      eqVal(m, v1, v2);
      return new Map();
    }

    function instList(m, flexSet, vl1, vl2) {
      if (vl1.length === 0 && vl2.length === 0) return new Map();
      const s1 = inst(m, flexSet, vl1[0], vl2[0]);
      const rest1 = vl1.slice(1).map(v => substVal(s1, v));
      const rest2 = vl2.slice(1).map(v => substVal(s1, v));
      const s2 = instList(m, flexSet, rest1, rest2);
      return compSubst(s1, s2);
    }

    function checkNoccEnv(k, j, env) {
      for (const b of env) {
        if (!nocc(k, { tag: 'VGen', k: j }, b.val)) {
          throw new Error("unsound size refinement in pattern: size variable occurs in another pattern variable's type");
        }
      }
    }

    function checkNoccDomains(k, j, v) {
      if (v.tag === 'VPi') {
        if (!nocc(k, { tag: 'VGen', k: j }, v.dom)) {
          throw new Error('unsound size refinement in pattern: size variable shared across multiple arguments or branches');
        }
        const bv = whnf(updateEnv(v.env, v.name, { tag: 'VGen', k }), v.cod);
        checkNoccDomains(k + 1, j, bv);
      }
    }

    function checkPattern(k, flex, ins, rho, gamma, v, p) {
      const vf = force(v);
      if (vf.tag !== 'VPi') throw new Error(`checkpattern ${showVal(vf)}`);
      if (p.tag === 'VarP') {
        const gk = { tag: 'VGen', k };
        const bv = whnf(updateEnv(vf.env, vf.name, gk), vf.cod);
        return {
          k: k + 1, flex, ins,
          rho: updateEnv(rho, p.name, gk),
          gamma: updateEnv(gamma, p.name, vf.dom),
          v: bv
        };
      }
      if (p.tag === 'DotP') {
        const gk = { tag: 'VGen', k };
        const bv = whnf(updateEnv(vf.env, vf.name, gk), vf.cod);
        return {
          k: k + 1,
          flex: [{ k, expr: p.expr, tv: vf.dom }, ...flex],
          ins, rho, gamma, v: bv
        };
      }
      if (p.tag === 'SuccP') {
        const st = whnf([], { tag: 'Pi', name: '', dom: { tag: 'Size' }, cod: { tag: 'Size' } });
        const r = checkPattern(k, flex, ins, rho, gamma, st, p.pat);
        eqVal(r.k, vf.dom, { tag: 'VSize' });
        const pv = p2v(k, p).val;
        const vb = whnf(updateEnv(vf.env, vf.name, pv), vf.cod);
        return { k: r.k, flex: r.flex, ins: r.ins, rho: r.rho, gamma: r.gamma, v: vb };
      }
      if (p.tag === 'ConP') {
        const entry = currentSig.get(p.name);
        const r = checkPatterns(k, flex, ins, rho, gamma, entry.ty, p.args);
        const flexSet = new Set(r.flex.map(x => x.k));
        const subst = inst(r.k, flexSet, r.v, vf.dom);
        const pv = p2v(k, p).val;
        let vb = whnf(updateEnv(vf.env, vf.name, pv), vf.cod);
        const ins2 = compSubst(r.ins, subst);
        if (mode === 'fixed') {
          // Bug 1 Fix: Enforce the Pattern-Refinement Invariant!
          for (const item of r.flex) {
            if (item.tv.tag === 'VSize' && !ins.has(item.k)) {
              const val = ins2.get(item.k);
              if (val && val.tag === 'VSucc') {
                checkNoccEnv(r.k, item.k, gamma);
                checkNoccDomains(r.k, item.k, vb);
              }
            }
          }
        }
        vb = substVal(ins2, vb);
        const gamma2 = substEnv(ins2, r.gamma);
        return { k: r.k, flex: r.flex, ins: ins2, rho: r.rho, gamma: gamma2, v: vb };
      }
    }

    function checkPatterns(k, flex, ins, rho, gamma, v, pats) {
      let state = { k, flex, ins, rho, gamma, v };
      for (const p of pats) {
        state = checkPattern(state.k, state.flex, state.ins, state.rho, state.gamma, state.v, p);
      }
      return state;
    }

    function checkDot(k, rho, gamma, subst, item) {
      const v = subst.get(item.k);
      if (!v) throw new Error('dot pattern variable not instantiated');
      const tv = substVal(subst, item.tv);
      checkExpr(k, rho, gamma, item.expr, tv);
      const v2 = whnf(rho, item.expr);
      eqVal(k, v, v2);
    }

    // Process all top-level declarations
    for (const d of adecls) {
      if (d.tag === 'DataDecl') {
        const tt = teleToType(d.tele, d.ts.ty);
        const params = d.tele.length;
        const p2 = d.sz === 'Sized' ? params + 1 : params;
        checkDataType(0, [], [], p2, tt);
        if (d.sz === 'Sized') {
          const { tele } = typeToTele(tt);
          if (!tele[params] || tele[params].ty.tag !== 'Size') {
            throw new Error(`${d.ts.name} misses size index`);
          }
        }
        const vt = whnf([], tt);
        currentSig.set(d.ts.name, { kind: 'DataSig', co: d.co, sz: d.sz, posList: d.posList, ty: vt });
        for (const c of d.cons) {
          const ctt = teleToType(d.tele, c.ty);
          checkConType(0, [], [], p2, ctt);
          const vct = whnf([], ctt);
          sposConstructor(d.ts.name, 0, d.posList, vct, mode);
          currentSig.set(c.name, { kind: 'ConSig', ty: vct });
          if (d.sz === 'Sized') {
            szConstructor(d.ts.name, params, vct);
          }
        }
      } else if (d.tag === 'LetDecl') {
        checkType(0, [], [], d.ts.ty);
        const vt = whnf([], d.ts.ty);
        checkExpr(0, [], [], d.body, vt);
        const vbody = whnf([], d.body);
        currentSig.set(d.ts.name, { kind: 'LetSig', ty: vt, val: vbody });
      } else if (d.tag === 'FunDecl') {
        for (const f of d.funs) {
          const vt = whnf([], f.ts.ty);
          currentSig.set(f.ts.name, { kind: 'FunSig', co: d.co, ty: vt, clauses: f.clauses, enabled: false });
        }
        let allAdm = true;
        for (const f of d.funs) {
          checkType(0, [], [], f.ts.ty);
          const vt = whnf([], f.ts.ty);
          const adm = d.co === 'Ind' ? szCheckIndFun(0, vt) : szCheckCoFun(0, vt);
          const comp = d.co === 'Ind' ? completePatterns(f.clauses, mode) : true;
          if (!adm) {
            const msg = `${f.ts.name} : type not admissble`;
            output.push(msg);
            diagnostics.push({ type: 'admissibility', fn: f.ts.name, message: msg });
          }
          if (!comp) {
            const msg = `${f.ts.name} : size pattern incomplete`;
            output.push(msg);
            diagnostics.push({ type: 'completeness', fn: f.ts.name, message: msg });
          }
          if (!adm || !comp) allAdm = false;
        }
        for (const f of d.funs) {
          const vt = whnf([], f.ts.ty);
          for (let ci = 0; ci < f.clauses.length; ci++) {
            const cl = f.clauses[ci];
            try {
              const r = checkPatterns(0, [], new Map(), [], [], vt, cl.pats);
              for (const item of r.flex) {
                checkDot(r.k, r.rho, r.gamma, r.ins, item);
              }
              checkExpr(r.k, r.rho, r.gamma, cl.rhs, r.v);
            } catch (err) {
              throw new Error(`error during typechecking:\n${f.ts.name} -> clause ${ci + 1} -> ${err.message}`);
            }
          }
        }
        const term = terminationCheck(d.funs, mode);
        for (const cm of term.initialCalls) {
          callMatrices.push({
            caller: cm.caller,
            callee: cm.callee,
            matrix: cm.m.map(r => r.map(showOrder))
          });
        }
        if (!term.ok) {
          const msg = d.funs.length === 1
            ? `Termination check for function ${d.funs[0].ts.name} fails`
            : `Termination check for mutual block ${JSON.stringify(d.funs.map(x => x.ts.name))} fails for ${JSON.stringify(term.failed)}`;
          output.push(msg);
          diagnostics.push({ type: 'termination', fn: term.failed.join(', '), message: msg });
        }
        if (allAdm && term.ok) {
          for (const f of d.funs) {
            const entry = currentSig.get(f.ts.name);
            entry.enabled = true;
          }
        }
      }
    }

    output.push('--- evaluating ---');
    for (const d of adecls) {
      if (d.tag === 'LetDecl' && d.evalFlag) {
        const entry = currentSig.get(d.ts.name);
        output.push(`${d.ts.name} evaluates to ${showVal(entry.val)}`);
      }
    }

    return {
      ok: diagnostics.length === 0,
      output: output.join('\n'),
      diagnostics,
      callMatrices
    };
  }

  return { runProgram };
});
