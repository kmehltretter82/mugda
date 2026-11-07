#!/usr/bin/env node
// Differential test: browser playground engine (docs/mugda-engine.js, mode 'fixed')
// versus the reference Lean 4 checker (.lake/build/bin/mugda).
//
// For every examples/**/*.ma (except fragments under src/), both engines are run and
// their observable verdicts are compared:
//   * verdict class   : 'error' (parse/scope/type error), 'warnings', or 'ok'
//   * warning kinds   : set of {termination, incomplete, admissibility}
//   * eval results    : the "x evaluates to v" lines (only when no error)
//
// Known, documented divergences live in tests/js-divergences.txt
// (one "path  # reason" per line). A listed file that no longer diverges is
// reported so the list can be pruned.
//
//   node tests/js-vs-lean.mjs            run the comparison (exit 1 on new divergence)
//   node tests/js-vs-lean.mjs --verbose  also print details for known divergences

import { readFileSync, readdirSync, statSync, existsSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
process.chdir(root);
const require = createRequire(import.meta.url);
const Engine = require('../docs/mugda-engine.js');
const MUGDA = process.env.MUGDA || '.lake/build/bin/mugda';
const verbose = process.argv.includes('--verbose');

function walk(dir) {
  let out = [];
  for (const name of readdirSync(dir).sort()) {
    const p = join(dir, name);
    if (statSync(p).isDirectory()) { if (name !== 'src') out = out.concat(walk(p)); }
    else if (name.endsWith('.ma')) out.push(p);
  }
  return out;
}

function warningKinds(lines) {
  const kinds = new Set();
  for (const l of lines) {
    if (/Termination check.*fails/.test(l)) kinds.add('termination');
    else if (/size pattern incomplete/.test(l)) kinds.add('incomplete');
    else if (/type not admiss/.test(l)) kinds.add('admissibility');
  }
  return [...kinds].sort();
}

function evalLines(lines) {
  return lines.filter(l => / evaluates to /.test(l) || /^eval error in /.test(l));
}

function leanVerdict(file) {
  const r = spawnSync(MUGDA, [file], { encoding: 'utf8', timeout: 60000 });
  const lines = (r.stdout || '').split('\n');
  const isError = r.status !== 0 && !lines.includes('--- evaluating ---');
  const warn = warningKinds(lines);
  return {
    cls: isError ? 'error' : (warn.length ? 'warnings' : 'ok'),
    warn: isError ? [] : warn,
    evals: isError ? [] : evalLines(lines),
    detail: isError ? ((r.stderr || '') + lines.filter(l => l && !l.startsWith('*****') && !l.startsWith('---')).join(' | ')).trim() : '',
  };
}

function jsVerdict(file) {
  try {
    const res = Engine.runProgram(readFileSync(file, 'utf8'), { mode: 'fixed', maxEvalSteps: 200000 });
    const lines = res.output.split('\n');
    const warn = warningKinds(lines);
    return { cls: warn.length ? 'warnings' : 'ok', warn, evals: evalLines(lines), detail: '' };
  } catch (e) {
    return { cls: 'error', warn: [], evals: [], detail: String(e && e.message || e).split('\n').join(' | ') };
  }
}

const known = new Map();
if (existsSync('tests/js-divergences.txt')) {
  for (const raw of readFileSync('tests/js-divergences.txt', 'utf8').split('\n')) {
    const line = raw.trim();
    if (!line || line.startsWith('#')) continue;
    const [path, ...rest] = line.split('#');
    known.set(path.trim(), rest.join('#').trim());
  }
}

let agree = 0, newDiv = 0, knownDiv = 0, fixed = 0;
for (const f of walk('examples')) {
  const L = leanVerdict(f), J = jsVerdict(f);
  const diffs = [];
  if (L.cls !== J.cls) diffs.push(`verdict lean=${L.cls} js=${J.cls}`);
  else if (JSON.stringify(L.warn) !== JSON.stringify(J.warn)) diffs.push(`warnings lean=[${L.warn}] js=[${J.warn}]`);
  if (L.cls !== 'error' && J.cls !== 'error' && JSON.stringify(L.evals) !== JSON.stringify(J.evals)) diffs.push('eval output differs');
  const isKnown = known.has(f);
  if (!diffs.length) {
    agree++;
    if (isKnown) { fixed++; console.log(`NOW-AGREES  ${f}  (remove from tests/js-divergences.txt)`); }
    continue;
  }
  if (isKnown) {
    knownDiv++;
    if (verbose) console.log(`known       ${f}: ${diffs.join('; ')}  # ${known.get(f)}`);
    continue;
  }
  newDiv++;
  console.log(`DIVERGES    ${f}: ${diffs.join('; ')}`);
  if (L.detail) console.log(`    lean: ${L.detail.slice(0, 300)}`);
  if (J.detail) console.log(`    js:   ${J.detail.slice(0, 300)}`);
  if (diffs.includes('eval output differs')) {
    console.log(`    lean evals: ${L.evals.join(' || ').slice(0, 400)}`);
    console.log(`    js   evals: ${J.evals.join(' || ').slice(0, 400)}`);
  }
}
console.log(`js-vs-lean: ${agree} agree, ${knownDiv} known divergences, ${newDiv} new divergences` + (fixed ? `, ${fixed} stale allowlist entries` : ''));
process.exit(newDiv || fixed ? 1 : 0);
