/-
  MugdaCore.lean
  ==============
  Constructive, 100% total Lean 4 port of the Mugda core compiler:
    1. `Abstract.hs`     — Core AST (`Expr`, `Pattern`, `Clause`, `Declaration`, telescopes)
    2. `Completness.hs`  — Size pattern completeness checker (`completePatterns`)
    3. `Value.hs`        — First-order strictly positive `Val` domain, pure `TypeCheck` monad,
                           fuel-bounded total `whnf`, `app`, `force`, `matchPat`, `nocc`
    4. `SPos.hs`         — Strict positivity checker (`sposConstructor`, `spos`)
    5. `Termination.hs`  — Extended Matrix Order (`Order`, `comp`, `maxO`, `minO`, `collapse`),
                           call extraction (`collectCallsExpr`), Kleene closure (`complete`),
                           and Size-Change Termination (`terminationCheckFuns`)
    6. `TypeChecker.hs`  — Conversion & size subtyping (`eqVal`, `leqVal`, `leqSize`),
                           pattern unification (`inst`), dependent pattern checking
                           (`checkPattern` with `checkNoccEnv` & `checkNoccDomains`),
                           admissibility (`szCheckIndFun`, `szCheckCoFun`, `szUsed'`),
                           and bidirectional checking (`checkExpr`, `inferExpr`, `typeCheckDecls`)
    7. In-place constructive theorems & executable `#eval` / `native_decide` verification suite.

  Design rules:
    - Zero `partial`, zero `unsafe`, zero `sorry`, zero external library dependencies.
    - Every function is total and transparent to Lean 4's proof kernel.
-/

namespace MugdaCore

/-! ## 1. Port of `Abstract.hs` (Core Syntax) -/

abbrev Name := String

inductive Sized : Type where
  | Sized    : Sized
  | NotSized : Sized
  deriving DecidableEq, Repr, Inhabited, BEq

inductive Co : Type where
  | Ind   : Co
  | CoInd : Co
  deriving DecidableEq, Repr, Inhabited, BEq

inductive Pos : Type where
  | SPos  : Pos
  | NSPos : Pos
  deriving DecidableEq, Repr, Inhabited, BEq

inductive Expr : Type where
  | Set   : Expr
  | Size  : Expr
  | Succ  : Expr → Expr
  | Infty : Expr
  | Var   : Name → Expr
  | Con   : Co → Name → Expr
  | Def   : Name → Expr
  | Let   : Name → Expr
  | LLet  : Name → Expr → Expr → Expr → Expr
  | App   : Expr → List Expr → Expr
  | Lam   : Name → Expr → Expr
  | Pi    : Name → Expr → Expr → Expr
  deriving Repr, Inhabited, BEq

abbrev MType := Expr

inductive TypeSig : Type where
  | mk : Name → MType → TypeSig
  deriving Repr, Inhabited, BEq

abbrev Constructor := TypeSig
abbrev TBind := Name × MType
abbrev Telescope := List TBind

inductive Pattern : Type where
  | VarP  : Name → Pattern
  | ConP  : Co → Name → List Pattern → Pattern
  | SuccP : Pattern → Pattern
  | DotP  : Expr → Pattern
  deriving Repr, Inhabited, BEq

inductive Clause : Type where
  | mk : List Pattern → Expr → Clause
  deriving Repr, Inhabited, BEq

inductive Declaration : Type where
  | DataDecl : Name → Sized → Co → List Pos → Telescope → MType → List Constructor → Declaration
  | FunDecl  : Co → List (TypeSig × List Clause) → Declaration
  | LetDecl  : Bool → TypeSig → Expr → Declaration
  deriving Repr, Inhabited, BEq

def teleToType : Telescope → MType → MType
  | [],            t2 => t2
  | (n, t) :: tel, t2 => Expr.Pi n t (teleToType tel t2)

def splitTeleType : Nat → Telescope × MType → Telescope × MType
  | 0,     (tel, t)             => (tel, t)
  | k + 1, (tel, Expr.Pi n t b) => splitTeleType k (tel ++ [(n, t)], b)
  | _,     (tel, t)             => (tel, t)

def typeToTeleAux : MType → Telescope → Telescope × MType
  | Expr.Pi n t1 t2, tel => typeToTeleAux t2 (tel ++ [(n, t1)])
  | x,               tel => (tel, x)

def typeToTele (t : MType) : Telescope × MType :=
  typeToTeleAux t []

mutual
  def prettyExpr : Expr → String
    | .Set            => "Set"
    | .Size           => "Size"
    | .Succ e         => "($ " ++ prettyExpr e ++ ")"
    | .Infty          => "#"
    | .Var n          => n
    | .Con _ n        => n
    | .Def n          => n
    | .Let n          => n
    | .LLet n t e1 e2 => "(let " ++ n ++ " : " ++ prettyExpr t ++ " = " ++ prettyExpr e1 ++ " in " ++ prettyExpr e2 ++ ")"
    | .App e1 el      => "(" ++ prettyExprs (e1 :: el) ++ ")"
    | .Lam x e1       => "(\\" ++ x ++ " -> " ++ prettyExpr e1 ++ ")"
    | .Pi "" t1 t2    => "(" ++ prettyExpr t1 ++ " -> " ++ prettyExpr t2 ++ ")"
    | .Pi x t1 t2     => "((" ++ x ++ " : " ++ prettyExpr t1 ++ ") -> " ++ prettyExpr t2 ++ ")"

  def prettyExprs : List Expr → String
    | []      => ""
    | [e]     => prettyExpr e
    | e :: es => prettyExpr e ++ " " ++ prettyExprs es
end

/-! ## 2. Port of `Completness.hs` (Size Pattern Completeness) -/

mutual
  def cp : Pattern → Bool
    | .SuccP _      => false
    | .ConP _ _ pl  => cpList pl
    | .VarP _       => true
    | .DotP _       => true

  def cpList : List Pattern → Bool
    | []      => true
    | p :: pl => cp p && cpList pl
end

def completeClause : Clause → Bool
  | .mk pl _ => cpList pl

def completePatterns (cl : List Clause) : Bool :=
  cl.all completeClause

/-! ## 3. Port of `Value.hs` (Semantic Domain, Pure Monad & Fuel-Bounded NbE) -/

/-- First-order, strictly positive semantic value domain (`Value.hs` lines 20–30).
    Closures are represented via explicit `List (Name × Val)` environments and `Expr`
    bodies, avoiding negative functional occurrences. -/
inductive Val : Type where
  | VSet   : Val
  | VSize  : Val
  | VInfty : Val
  | VSucc  : Val → Val
  | VApp   : Val → List Val → Val
  | VCon   : Co → Name → Val
  | VDef   : Name → Val
  | VGen   : Nat → Val
  | VPi    : Name → Val → List (Name × Val) → Expr → Val
  | VLam   : Name → List (Name × Val) → Expr → Val
  deriving Repr, Inhabited

mutual
  def valBeq : Val → Val → Bool
    | .VSet,            .VSet            => true
    | .VSize,           .VSize           => true
    | .VInfty,          .VInfty          => true
    | .VSucc v1,        .VSucc v2        => valBeq v1 v2
    | .VApp u1 vs1,     .VApp u2 vs2     => valBeq u1 u2 && valBeqList vs1 vs2
    | .VCon c1 n1,      .VCon c2 n2      => c1 == c2 && n1 == n2
    | .VDef n1,         .VDef n2         => n1 == n2
    | .VGen k1,         .VGen k2         => k1 == k2
    | .VPi x1 a1 e1 b1, .VPi x2 a2 e2 b2 => x1 == x2 && valBeq a1 a2 && valBeqEnv e1 e2 && b1 == b2
    | .VLam x1 e1 b1,   .VLam x2 e2 b2   => x1 == x2 && valBeqEnv e1 e2 && b1 == b2
    | _,                _                => false

  def valBeqList : List Val → List Val → Bool
    | [],       []       => true
    | v1 :: r1, v2 :: r2 => valBeq v1 v2 && valBeqList r1 r2
    | _,        _        => false

  def valBeqEnv : List (Name × Val) → List (Name × Val) → Bool
    | [],             []             => true
    | (x1, v1) :: r1, (x2, v2) :: r2 => x1 == x2 && valBeq v1 v2 && valBeqEnv r1 r2
    | _,              _              => false
end

instance : BEq Val := ⟨valBeq⟩

@[simp] theorem Val.beq_vset : (Val.VSet == Val.VSet) = true := rfl
@[simp] theorem Val.bne_vset : (Val.VSet != Val.VSet) = false := rfl
@[simp] theorem Val.beq_vsize : (Val.VSize == Val.VSize) = true := rfl
@[simp] theorem Val.bne_vsize : (Val.VSize != Val.VSize) = false := rfl
@[simp] theorem Val.beq_vinfty : (Val.VInfty == Val.VInfty) = true := rfl
@[simp] theorem Val.bne_vinfty : (Val.VInfty != Val.VInfty) = false := rfl
@[simp] theorem Val.beq_vgen (k1 k2 : Nat) : (Val.VGen k1 == Val.VGen k2) = (k1 == k2) := rfl
@[simp] theorem Val.bne_vgen (k1 k2 : Nat) : (Val.VGen k1 != Val.VGen k2) = (k1 != k2) := rfl

abbrev TVal := Val
abbrev Env := List (Name × Val)

def emptyEnv : Env := []

def updateEnv (env : Env) (n : Name) (v : Val) : Env :=
  if n == "" then env else (n, v) :: env

def lookupEnvOpt : Env → Name → Option Val
  | [],          _ => none
  | (x, v) :: xs, n => if x == n then some v else lookupEnvOpt xs n

inductive SigDef : Type where
  | FunSig  : Co → TVal → List Clause → Bool → SigDef
  | LetSig  : TVal → Expr → SigDef
  | ConSig  : TVal → SigDef
  | DataSig : Nat → List Pos → Sized → Co → TVal → SigDef
  deriving Repr, Inhabited, BEq

abbrev Signature := List (Name × SigDef)

def emptySig : Signature := []

def lookupSigOpt (n : Name) : Signature → Option SigDef
  | []            => none
  | (k, d) :: rest => if k == n then some d else lookupSigOpt n rest

def addSig (sig : Signature) (n : Name) (d : SigDef) : Signature :=
  (n, d) :: sig.filter (fun (k, _) => k != n)

/-- Pure state + exception monad replacing Haskell's `StateT Signature (ErrorT TraceError IO)`. -/
structure TCState where
  sig      : Signature := emptySig
  warnings : List String := []
  deriving Repr, Inhabited

abbrev TypeCheck (α : Type) := StateT TCState (Except String) α

def runTypeCheck (st : TCState) (m : TypeCheck α) : Except String (α × TCState) :=
  StateT.run m st

def getSig : TypeCheck Signature := do
  let st ← get
  pure st.sig

def putSig (s : Signature) : TypeCheck Unit := do
  modify fun st => { st with sig := s }

def addWarning (msg : String) : TypeCheck Unit := do
  modify fun st => { st with warnings := st.warnings ++ [msg] }

def throwErrorMsg (msg : String) : TypeCheck α :=
  throw msg

def throwTrace (m : TypeCheck α) (ctx : String) : TypeCheck α :=
  tryCatch m (fun err => throw (ctx ++ ": " ++ err))

def lookupSig (n : Name) : TypeCheck SigDef := do
  let sig ← getSig
  match lookupSigOpt n sig with
  | some d => pure d
  | none   => throwErrorMsg ("Error not in signature: " ++ n)

def lookupEnv (env : Env) (n : Name) : TypeCheck Val :=
  match lookupEnvOpt env n with
  | some v => pure v
  | none   => throwErrorMsg ("lookup env error " ++ n)

/-- At `#` (`VInfty`), `$ # = #` (`Value.hs` lines 129–132). -/
def sinfty : Val → Val
  | .VInfty => .VInfty
  | v       => .VSucc v

/-- Default evaluation fuel for NbE and type checking. -/
def defaultFuel : Nat := 1000

/-- 3-valued pattern matching result (`matched` vs `mismatch` vs `stuck`).
    Distinguishing constructor mismatch (`zero` vs `succ y`) from neutral stuckness
    (`zero` vs `.VGen k`) prevents `matchClauses` from unsoundly falling through an
    earlier constructor pattern into a later catch-all variable pattern during open
    conversion checking. -/
inductive MatchResult (α : Type) where
  | matched  : α → MatchResult α
  | mismatch : MatchResult α
  | stuck    : MatchResult α
  deriving DecidableEq, Repr, Inhabited, BEq

def MatchResult.map (f : α → β) : MatchResult α → MatchResult β
  | .matched a => .matched (f a)
  | .mismatch  => .mismatch
  | .stuck     => .stuck

mutual
  def whnf (fuel : Nat) (env : Env) (e : Expr) : TypeCheck Val :=
    match fuel with
    | 0 => throwErrorMsg "whnf: out of fuel"
    | fuel' + 1 =>
      match e with
      | .LLet x _ e1 e2 => do
          let v1 ← whnf fuel' env e1
          whnf fuel' (updateEnv env x v1) e2
      | .Lam x e1 => pure (.VLam x env e1)
      | .Pi x a b => do
          let av ← whnf fuel' env a
          pure (.VPi x av env b)
      | .App e1 el => do
          let v1 ← whnf fuel' env e1
          let vl ← whnfList fuel' env el
          app fuel' v1 vl
      | .Set     => pure .VSet
      | .Infty   => pure .VInfty
      | .Succ e1 => do
          let v ← whnf fuel' env e1
          pure (sinfty v)
      | .Size    => pure .VSize
      | .Con co n => pure (.VCon co n)
      | .Def n   => pure (.VDef n)
      | .Let n   => do
          let d ← lookupSig n
          match d with
          | .LetSig _ eBody => whnf fuel' [] eBody
          | _ => throwErrorMsg ("Expected LetSig for " ++ n)
      | .Var y   => lookupEnv env y

  def whnfList (fuel : Nat) (env : Env) (es : List Expr) : TypeCheck (List Val) :=
    match fuel with
    | 0 => throwErrorMsg "whnfList: out of fuel"
    | fuel' + 1 =>
      match es with
      | []      => pure []
      | e :: rest => do
          let v ← whnf fuel' env e
          let vs ← whnfList fuel' env rest
          pure (v :: vs)

  def app (fuel : Nat) (u : Val) (c : List Val) : TypeCheck Val :=
    match fuel with
    | 0 => throwErrorMsg "app: out of fuel"
    | fuel' + 1 =>
      match c with
      | [] => pure u
      | v :: vl =>
        match u with
        | .VApp u2 c2 => app fuel' u2 (c2 ++ c)
        | .VLam x env e => do
            let v' ← whnf fuel' (updateEnv env x v) e
            app fuel' v' vl
        | .VDef n => appDef fuel' n c
        | _ => pure (.VApp u c)

  def force (fuel : Nat) (v : Val) : TypeCheck Val :=
    match fuel with
    | 0 => throwErrorMsg "force: out of fuel"
    | fuel' + 1 =>
      match v with
      | .VDef n => do
          let d ← lookupSig n
          match d with
          | .FunSig .CoInd _ cl true => do
              let m ← matchClauses fuel' cl []
              match m with
              | some v' => force fuel' v'
              | none    => pure v
          | _ => pure v
      | .VApp (.VDef n) vl => do
          let d ← lookupSig n
          match d with
          | .FunSig .CoInd _ cl true => do
              let m ← matchClauses fuel' cl vl
              match m with
              | some v' => force fuel' v'
              | none    => pure v
          | _ => pure v
      | _ => pure v

  def appDef (fuel : Nat) (n : Name) (vl : List Val) : TypeCheck Val :=
    match fuel with
    | 0 => throwErrorMsg "appDef: out of fuel"
    | fuel' + 1 => do
        let d ← lookupSig n
        match d with
        | .FunSig .Ind _ cl true => do
            let m ← matchClauses fuel' cl vl
            match m with
            | none    => pure (.VApp (.VDef n) vl)
            | some v2 => pure v2
        | _ => pure (.VApp (.VDef n) vl)

  def matchClauses (fuel : Nat) (cls : List Clause) (cll : List Val) : TypeCheck (Option Val) :=
    match fuel with
    | 0 => throwErrorMsg "matchClauses: out of fuel"
    | fuel' + 1 =>
      match cls with
      | []                 => pure none
      | .mk pl rhs :: cl2  => do
          let x ← matchClause fuel' [] pl rhs cll
          match x with
          | .matched v => pure (some v)
          | .mismatch  => matchClauses fuel' cl2 cll
          | .stuck     => pure none

  def matchClause (fuel : Nat) (env : Env) (pats : List Pattern) (rhs : Expr) (vals : List Val) : TypeCheck (MatchResult Val) :=
    match fuel with
    | 0 => throwErrorMsg "matchClause: out of fuel"
    | fuel' + 1 =>
      match pats, vals with
      | [],      vl => do
          let v ← whnf fuel' env rhs
          let v2 ← app fuel' v vl
          pure (.matched v2)
      | p :: pl, v :: vl => do
          let m ← matchPat fuel' env p v
          match m with
          | .matched env' => matchClause fuel' env' pl rhs vl
          | .mismatch     => pure .mismatch
          | .stuck        => pure .stuck
      | _ :: _,  [] => pure .stuck

  def matchPat (fuel : Nat) (env : Env) (p : Pattern) (v0 : Val) : TypeCheck (MatchResult Env) :=
    match fuel with
    | 0 => throwErrorMsg "matchPat: out of fuel"
    | fuel' + 1 => do
        let v ← match p with
          | .ConP .CoInd _ _ => force fuel' v0
          | _                => pure v0
        match p, v with
        | .DotP _,            _                    => pure (.matched env)
        | .VarP x,            _                    => pure (.matched (updateEnv env x v))
        | .ConP _ x [],       .VCon _ y            => if x == y then pure (.matched env) else pure .mismatch
        | .ConP _ x (_ :: _), .VCon _ y            => if x == y then pure .stuck else pure .mismatch
        | .ConP _ x pl,       .VApp (.VCon _ y) vl => if x == y then matchList fuel' env pl vl else pure .mismatch
        | .ConP _ _ _,        _                    => pure .stuck
        | .SuccP p',          .VInfty              => matchPat fuel' env p' .VInfty
        | .SuccP p',          .VSucc v'            => matchPat fuel' env p' v'
        | .SuccP _,           _                    => pure .stuck

  def matchList (fuel : Nat) (env : Env) (pats : List Pattern) (vals : List Val) : TypeCheck (MatchResult Env) :=
    match fuel with
    | 0 => throwErrorMsg "matchList: out of fuel"
    | fuel' + 1 =>
      match pats, vals with
      | [],      []      => pure (.matched env)
      | p :: pl, v :: vl => do
          let m ← matchPat fuel' env p v
          match m with
          | .matched env' => matchList fuel' env' pl vl
          | .mismatch     => pure .mismatch
          | .stuck        => pure .stuck
      | _,       _       => pure .stuck
end

/- Semantic non-occurrence check (`Value.hs` lines 228–245). -/
mutual
  def nocc (fuel : Nat) (k : Nat) (a : Val) (tv : TVal) : TypeCheck Bool :=
    match fuel with
    | 0 => throwErrorMsg "nocc: out of fuel"
    | fuel' + 1 =>
      match tv with
      | .VPi x av env b => do
          let no ← nocc fuel' k a av
          if no then
            let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
            nocc fuel' (k + 1) a bv
          else
            pure false
      | .VLam x env b => do
          let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
          nocc fuel' (k + 1) a bv
      | .VSucc v => nocc fuel' k a v
      | .VApp v1 vl => do
          let n ← nocc fuel' k a v1
          let nl ← noccList fuel' k a vl
          pure (n && nl)
      | .VGen i =>
          match a with
          | .VGen j => pure (j != i)
          | _       => pure (a != .VGen i)
      | _ => pure (a != tv)

  def noccList (fuel : Nat) (k : Nat) (a : Val) (vs : List Val) : TypeCheck Bool :=
    match fuel with
    | 0 => throwErrorMsg "noccList: out of fuel"
    | fuel' + 1 =>
      match vs with
      | []        => pure true
      | v :: rest => do
          let b1 ← nocc fuel' k a v
          let b2 ← noccList fuel' k a rest
          pure (b1 && b2)
end

/-! ## 4. Port of `SPos.hs` (Strict Positivity Checker) -/

def posGen : Nat → List Pos → List Val
  | _, []           => []
  | i, .SPos :: pl  => .VGen i :: posGen (i + 1) pl
  | i, .NSPos :: pl => posGen (i + 1) pl

def posArgs : List Val → List Pos → List Val × List Val
  | [],      _            => ([], [])
  | _,       []           => ([], [])
  | v :: vs, .SPos :: ps  =>
      let (l1, l2) := posArgs vs ps
      (v :: l1, l2)
  | v :: vs, .NSPos :: ps =>
      let (l1, l2) := posArgs vs ps
      (l1, v :: l2)

mutual
  def spos (fuel : Nat) (k : Nat) (a : Val) (tv : TVal) : TypeCheck Bool :=
    match fuel with
    | 0 => throwErrorMsg "spos: out of fuel"
    | fuel' + 1 =>
      if a == tv then
        pure true
      else
        match tv with
        | .VPi x av env b => do
            let no ← nocc fuel' k a av
            if no then
              let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
              spos fuel' (k + 1) a bv
            else
              pure false
        | .VLam x env b => do
            let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
            spos fuel' (k + 1) a bv
        | .VSucc v => spos fuel' k a v
        | .VApp (.VDef m) vl => do
            let d ← lookupSig m
            match d with
            | .DataSig p pos _ _ _ => do
                let (pparams, nparams) := posArgs vl pos
                let rest := vl.drop p
                let sl ← sposList fuel' k a pparams
                let nl ← noccList fuel' k a (nparams ++ rest)
                pure (sl && nl)
            | _ => noccList fuel' k a vl
        | .VApp v1 vl => do
            let n ← nocc fuel' k a v1
            let nl ← noccList fuel' k a vl
            pure (n && nl)
        | _ => nocc fuel' k a tv

  def sposList (fuel : Nat) (k : Nat) (a : Val) (vs : List Val) : TypeCheck Bool :=
    match fuel with
    | 0 => throwErrorMsg "sposList: out of fuel"
    | fuel' + 1 =>
      match vs with
      | []        => pure true
      | v :: rest => do
          let b1 ← spos fuel' k a v
          let b2 ← sposList fuel' k a rest
          pure (b1 && b2)
end

def sposVals (fuel : Nat) (k : Nat) : List Val → TVal → TypeCheck Bool
  | [],      _  => pure true
  | i :: is, tv => do
      let b1 ← spos fuel k i tv
      let b2 ← sposVals fuel k is tv
      pure (b1 && b2)

/-- Strict positivity check for a constructor telescope (`SPos.hs` lines 17–28,
    including Bug 6 fix passing binder depth `k` into `spos` and `sposVals`). -/
def sposConstructor (fuel : Nat) (n : Name) (k : Nat) (sp : List Pos) (tv : TVal) : TypeCheck Unit :=
  match fuel with
  | 0 => throwErrorMsg "sposConstructor: out of fuel"
  | fuel' + 1 =>
    match tv with
    | .VPi x av env b => do
        let spr ← spos fuel' k (.VDef n) av
        let spv ← sposVals fuel' k (posGen 0 sp) av
        match spr, spv with
        | true, true => do
            let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
            sposConstructor fuel' n (k + 1) sp bv
        | false, _    => throwErrorMsg "rec. arg not strictly positive"
        | true, false => throwErrorMsg "parameter not strictly positive"
    | _ => pure ()

/-! ## 5. Port of `Termination.hs` (Matrix Order `ORDER_+` & Size-Change Termination) -/

inductive Order : Type where
  | Lt  : Order
  | Le  : Order
  | Un  : Order
  | Mat : List (List Order) → Order
  deriving Repr, Inhabited, BEq

abbrev Vector (α : Type) := List α
abbrev Matrix (α : Type) := List (Vector α)

def getElemOpt : List α → Nat → Option α
  | [],      _     => none
  | x :: _,  0     => some x
  | _ :: xs, i + 1 => getElemOpt xs i

def diagAux (i : Nat) : List (Vector α) → Vector α
  | []          => []
  | row :: rest =>
      match getElemOpt row i with
      | some x => x :: diagAux (i + 1) rest
      | none   => []

def diag (m : Matrix α) : Vector α :=
  diagAux 0 m

def minScalar : Order → Order → Order
  | .Un, _   => .Un
  | _,   .Un => .Un
  | .Lt, .Lt => .Lt
  | .Lt, .Le => .Le
  | .Le, .Lt => .Le
  | .Le, .Le => .Le
  | _,   _   => .Un

def maxScalar : Order → Order → Order
  | _,   .Lt => .Lt
  | .Lt, _   => .Lt
  | .Un, .Le => .Le
  | .Le, .Un => .Le
  | .Le, .Le => .Le
  | _,   _   => .Un

def compScalar : Order → Order → Order
  | .Lt, .Lt => .Lt
  | .Lt, .Le => .Lt
  | .Le, .Lt => .Lt
  | .Le, .Le => .Le
  | _,   _   => .Un

/- Structurally recursive collapse of an `Order` (or `Matrix Order`) to `{Lt, Le, Un}`. -/
mutual
  def collapseOrder : Order → Order
    | .Lt    => .Lt
    | .Le    => .Le
    | .Un    => .Un
    | .Mat m => collapseRows 0 m

  def collapseElemAt : Nat → List Order → Order
    | _,     []      => .Un
    | 0,     o :: _  => collapseOrder o
    | i + 1, _ :: os => collapseElemAt i os

  def collapseRows : Nat → List (List Order) → Order
    | _, []        => .Un
    | i, [r]       => collapseElemAt i r
    | i, r :: rows => minScalar (collapseElemAt i r) (collapseRows (i + 1) rows)
end

def collapse (m : Matrix Order) : Order :=
  collapseOrder (.Mat m)

/-- Fixed `maxO` (`Termination.hs` lines 34–43, Bug 3b fix: `.Un` is the additive identity,
    while combining two non-`Un` `Mat` values collapses both to scalars). -/
def maxO : Order → Order → Order
  | _,   .Lt => .Lt
  | .Lt, _   => .Lt
  | .Un, o2  => o2
  | o1,  .Un => o1
  | o1,  o2  => maxScalar (collapseOrder o1) (collapseOrder o2)

def maxL : List Order → Order
  | []      => .Un
  | o :: os => os.foldl maxO o

def okMat (m1 m2 : Matrix α) : Bool :=
  m1.length == m2.length

mutual
  def minO : Order → Order → Order
    | .Mat m1, .Mat m2 =>
        if okMat m1 m2 then .Mat (minM m1 m2)
        else minScalar (collapse m1) (collapse m2)
    | o1, o2 => minScalar (collapseOrder o1) (collapseOrder o2)

  def minM : Matrix Order → Matrix Order → Matrix Order
    | [],        _         => []
    | _,         []        => []
    | r1 :: rs1, r2 :: rs2 => minV r1 r2 :: minM rs1 rs2

  def minV : Vector Order → Vector Order → Vector Order
    | [],        _         => []
    | _,         []        => []
    | x1 :: xs1, x2 :: xs2 => minO x1 x2 :: minV xs1 xs2
end

def minL : List Order → Order
  | []      => .Un
  | o :: os => os.foldl minO o

def transp (m : Matrix Order) : Matrix Order :=
  match m with
  | []       => []
  | [] :: _  => []
  | r0 :: _  =>
      (List.range r0.length).map fun j =>
        m.filterMap fun row => getElemOpt row j

mutual
  def comp : Order → Order → Order
    | .Mat m1, .Mat m2 =>
        if okMat m1 m2 then .Mat (mmulOrd m1 m2)
        else compScalar (collapse m1) (collapse m2)
    | .Mat m, .Le => .Mat m
    | .Le, .Mat m => .Mat m
    | o1, o2 => compScalar (collapseOrder o1) (collapseOrder o2)

  def scalarProdOrd : Vector Order → Vector Order → Order
    | [],      _       => .Un
    | _,       []      => .Un
    | x :: xs, y :: ys => maxO (comp x y) (scalarProdOrd xs ys)

  def mmulRow (r : Vector Order) : Matrix Order → Vector Order
    | []        => []
    | c :: cols => scalarProdOrd r c :: mmulRow r cols

  def mmulRows (cols : Matrix Order) : Matrix Order → Matrix Order
    | []        => []
    | r :: rows => mmulRow r cols :: mmulRows cols rows

  def mmulOrd (m1 m2 : Matrix Order) : Matrix Order :=
    mmulRows (transp m2) m1
end

mutual
  def isPurePat : Pattern → Bool
    | .VarP _         => true
    | .ConP .Ind _ pl => isPurePatList pl
    | _               => false

  def isPurePatList : List Pattern → Bool
    | []      => true
    | p :: ps => isPurePat p && isPurePatList ps
end

mutual
  def isPureExpr : Expr → Bool
    | .Var _                => true
    | .Con .Ind _           => true
    | .App (.Con .Ind _) el => isPureExprList el
    | .App (.Def _) el      => isPureExprList el
    | _                     => false

  def isPureExprList : List Expr → Bool
    | []      => true
    | e :: es => isPureExpr e && isPureExprList es
end

mutual
  def exprToPattern : Expr → Option Pattern
    | .Var n              => some (.VarP n)
    | .Succ e             => Option.map .SuccP (exprToPattern e)
    | .App (.Con co n) el => Option.map (.ConP co n) (exprsToPatterns el)
    | .Con co n           => some (.ConP co n [])
    | _                   => none

  def exprsToPatterns : List Expr → Option (List Pattern)
    | []      => some []
    | e :: el =>
        match exprToPattern e, exprsToPatterns el with
        | some p, some pl => some (p :: pl)
        | _,      _       => none
end

/- Variable comparison against a structural pattern (`compareVar` without `DotP`). -/
mutual
  def compareVarPure (n : Name) : Pattern → Order
    | .VarP n2                => if n == n2 then .Le else .Un
    | .ConP .Ind _ (p :: pl)  => comp .Lt (maxL (compareVarPure n p :: compareVarPureList n pl))
    | .SuccP p2               => comp .Lt (compareVarPure n p2)
    | _                       => .Un

  def compareVarPureList (n : Name) : List Pattern → List Order
    | []      => []
    | p :: ps => compareVarPure n p :: compareVarPureList n ps
end

def compareVar (n : Name) : Pattern → Order
  | .DotP e =>
      match exprToPattern e with
      | none    => .Un
      | some p' => compareVarPure n p'
  | p => compareVarPure n p

/- Expression-to-pattern comparison (`Termination.hs` lines 138–163, including Bug 3a fix
   restricting `Mat` to `co == Ind && isPurePatList pl && isPureExprList args`). -/
mutual
  def compareExpr (fuel : Nat) (e : Expr) (p : Pattern) : Order :=
    match fuel with
    | 0 => .Un
    | fuel' + 1 =>
      match e, p with
      | _, .DotP e' =>
          match exprToPattern e' with
          | none    => if e == e' then .Le else .Un
          | some p' => compareExpr fuel' e p'
      | .Var i, p => compareVar i p
      | .App (.Var i) _, p => compareVar i p
      | .Con _ n1, .ConP _ n2 [] => if n1 == n2 then .Le else .Un
      | .App (.Con _ n1) [e1], .ConP _ n2 [p1] =>
          if n1 == n2 then compareExpr fuel' e1 p1 else .Un
      | .App (.Con co n1) args, .ConP _ n2 pl =>
          if n1 == n2 && args.length == pl.length then
            if co == .Ind && isPurePatList pl && isPureExprList args then
              .Mat (compareMatRows fuel' args pl)
            else
              minL (compareConArgs fuel' args pl)
          else .Un
      | .Succ e2, .SuccP p2 => compareExpr fuel' e2 p2
      | _, _ => .Un

  def compareMatRow (fuel : Nat) (e : Expr) (pats : List Pattern) : List Order :=
    match fuel with
    | 0 => []
    | fuel' + 1 =>
      match pats with
      | []      => []
      | p :: ps => compareExpr fuel' e p :: compareMatRow fuel' e ps

  def compareMatRows (fuel : Nat) (args : List Expr) (pats : List Pattern) : Matrix Order :=
    match fuel with
    | 0 => []
    | fuel' + 1 =>
      match args with
      | []      => []
      | e :: es => compareMatRow fuel' e pats :: compareMatRows fuel' es pats

  def compareConArg (fuel : Nat) (e : Expr) (p : Pattern) : Order :=
    match fuel with
    | 0 => .Un
    | fuel' + 1 =>
      match e, p with
      | e, .DotP e' => if e == e' then .Le else .Un
      | .Succ _, _  => .Un
      | .Infty, _   => .Un
      | e, p        => compareExpr fuel' e p

  def compareConArgs (fuel : Nat) (es : List Expr) (ps : List Pattern) : List Order :=
    match fuel with
    | 0 => []
    | fuel' + 1 =>
      match es, ps with
      | [],      _        => []
      | _,       []       => []
      | e :: er, p :: pr  => compareConArg fuel' e p :: compareConArgs fuel' er pr
end

def compareArgs (pl : List Pattern) (el : List Expr) (ar_g : Nat) : Matrix Order :=
  match pl with
  | [] => [[]]
  | _  =>
    match el with
    | [] =>
      if ar_g > 0 then List.replicate ar_g (List.replicate pl.length .Un) else [[]]
    | _ =>
      let el' := if ar_g > 0 then el.take ar_g else el
      let diff := ar_g - el'.length
      let fill := if diff > 0 then List.replicate diff (List.replicate pl.length .Un) else []
      let cmp := el'.map fun e => pl.map (compareExpr 100 e)
      cmp ++ fill

structure Call where
  source : Name
  target : Name
  matrix : Matrix Order
  deriving Repr, Inhabited, BEq

def callComb (c1 c2 : Call) : Call :=
  { source := c2.source, target := c1.target, matrix := mmulOrd c1.matrix c2.matrix }

def cgComb (cg1 cg2 : List Call) : List Call :=
  cg1.foldr (fun c1 acc =>
    (cg2.filter (fun c2 => c1.source == c2.target)).map (callComb c1) ++ acc) []

def dedupCalls : List Call → List Call
  | []      => []
  | c :: cs =>
      let rest := dedupCalls cs
      if rest.contains c then rest else c :: rest

/-- Fuel-bounded Kleene-star call-graph closure (`Termination.hs` lines 247–260). -/
def completeCalls : Nat → List Call → List Call
  | 0,        cg => cg
  | fuel + 1, cg =>
      let cgs := dedupCalls cg
      let next := dedupCalls (cgs ++ cgComb cgs cgs)
      if next.all cgs.contains then cgs else completeCalls fuel next

/- Structurally recursive `isDecr` on `Order` and its diagonal. -/
mutual
  def isDecr : Order → Bool
    | .Lt    => true
    | .Mat m => isDecrRows 0 m
    | _      => false

  def isDecrElemAt : Nat → List Order → Bool
    | _,     []      => false
    | 0,     o :: _  => isDecr o
    | i + 1, _ :: os => isDecrElemAt i os

  def isDecrRows : Nat → List (List Order) → Bool
    | _, []        => false
    | i, r :: rows => isDecrElemAt i r || isDecrRows (i + 1) rows
end

def checkIdem (cg : Call) : Bool :=
  let cgcg := callComb cg cg
  !(cg == cgcg) || isDecr (.Mat cgcg.matrix)

def checkAll (calls : List Call) : Bool :=
  calls.all checkIdem

def arity : List Clause → Nat
  | []            => 0
  | .mk pl _ :: _ => pl.length

def collectNames : List (TypeSig × List Clause) → List (Name × Nat)
  | []                    => []
  | (.mk n _, cl) :: rest => (n, arity cl) :: collectNames rest

def lookupArity (g : Name) : List (Name × Nat) → Option Nat
  | []            => none
  | (n, a) :: rest => if n == g then some a else lookupArity g rest

/- Call extraction (`Termination.hs` lines 307–334, including Bug 4 fix for `LLet _ t1 e1 e2`). -/
mutual
  def collectCallsExpr (nl : List (Name × Nat)) (f : Name) (pl : List Pattern) : Expr → List Call
    | .App (.Def g) args =>
        let calls := collectCallsExprList nl f pl args
        match lookupArity g nl with
        | none      => calls
        | some ar_g =>
            let m := compareArgs pl args ar_g
            { source := f, target := g, matrix := m } :: calls
    | .Def g =>
        match lookupArity g nl with
        | none      => []
        | some ar_g =>
            let m := compareArgs pl [] ar_g
            [{ source := f, target := g, matrix := m }]
    | .App e args      => collectCallsExpr nl f pl e ++ collectCallsExprList nl f pl args
    | .Lam _ e1        => collectCallsExpr nl f pl e1
    | .LLet _ t1 e1 e2 =>
        collectCallsExpr nl f pl t1 ++
        collectCallsExpr nl f pl e1 ++
        collectCallsExpr nl f pl e2
    | .Pi _ e1 e2      => collectCallsExpr nl f pl e1 ++ collectCallsExpr nl f pl e2
    | .Succ e1         => collectCallsExpr nl f pl e1
    | _                => []

  def collectCallsExprList (nl : List (Name × Nat)) (f : Name) (pl : List Pattern) : List Expr → List Call
    | []      => []
    | e :: es => collectCallsExpr nl f pl e ++ collectCallsExprList nl f pl es
end

def collectClauses (nl : List (Name × Nat)) (f : Name) : List Clause → List Call
  | []               => []
  | .mk pl rhs :: cl => collectCallsExpr nl f pl rhs ++ collectClauses nl f cl

def collectCGFunDecl (funs : List (TypeSig × List Clause)) : List Call :=
  let nl := collectNames funs
  funs.foldr (fun (.mk n _, cl) acc => collectClauses nl n cl ++ acc) []

def terminationCheckFuns (funs : List (TypeSig × List Clause)) : List (Name × Bool) :=
  let names := (collectNames funs).map Prod.fst
  let cg := completeCalls 100 (collectCGFunDecl funs)
  let loops := cg.filter (fun c => c.target == c.source)
  names.map fun n =>
    let nCalls := loops.filter (fun c => c.source == n)
    (n, checkAll nCalls)

def terminationCheck (funs : List (TypeSig × List Clause)) : Bool :=
  (terminationCheckFuns funs).all Prod.snd

/-! ## 6. Port of `TypeChecker.hs` (Conversion, Subtyping, Pattern Unification & Admissibility) -/

inductive ForceHist : Type where
  | N : ForceHist
  | L : ForceHist
  | R : ForceHist
  deriving DecidableEq, Repr, Inhabited, BEq

def switchForce : ForceHist → ForceHist
  | .L => .R
  | .R => .L
  | .N => .N

/-- Substaging on size values (`TypeChecker.hs` lines 316–325). -/
def leqSize : Val → Val → TypeCheck Unit
  | _,        .VInfty   => pure ()
  | .VSucc v1, .VSucc v2 => leqSize v1 v2
  | v1,       .VSucc v2 => leqSize v1 v2
  | .VGen k1, .VGen k2  =>
      if k1 == k2 then pure ()
      else throwErrorMsg ("gen mismatch " ++ toString k1 ++ " " ++ toString k2)
  | _,        _         => throwErrorMsg "leqSize error"

mutual
  def eqVal' (fuel : Nat) (f : ForceHist) (k : Nat) (u1 u2 : Val) : TypeCheck Unit :=
    match fuel with
    | 0 => throwErrorMsg "eqVal': out of fuel"
    | fuel' + 1 => do
        let u1f ← force fuel' u1
        let u2f ← force fuel' u2
        if (u1f != u1) && !(u2f != u2) && (f != .R) then
          eqVal' fuel' .L k u1f u2
        else if !(u1f != u1) && (u2f != u2) && (f != .L) then
          eqVal' fuel' .R k u1 u2f
        else
          match u1, u2 with
          | .VSucc v1, .VSucc v2 => eqVal' fuel' f k v1 v2
          | .VApp v1 vl1, .VApp v2 vl2 => do
              eqVal' fuel' f k v1 v2
              eqVals' fuel' f k vl1 vl2
          | .VPi x1 av1 env1 b1, .VPi x2 av2 env2 b2 => do
              eqVal' fuel' f k av1 av2
              let v1 ← whnf fuel' (updateEnv env1 x1 (.VGen k)) b1
              let v2 ← whnf fuel' (updateEnv env2 x2 (.VGen k)) b2
              eqVal' fuel' f (k + 1) v1 v2
          | .VLam x1 env1 b1, .VLam x2 env2 b2 => do
              let v1 ← whnf fuel' (updateEnv env1 x1 (.VGen k)) b1
              let v2 ← whnf fuel' (updateEnv env2 x2 (.VGen k)) b2
              eqVal' fuel' f (k + 1) v1 v2
          | v1, v2 =>
              if v1 == v2 then pure ()
              else throwErrorMsg "eqVal error"

  def eqVals' (fuel : Nat) (f : ForceHist) (k : Nat) (vs1 vs2 : List Val) : TypeCheck Unit :=
    match fuel with
    | 0 => throwErrorMsg "eqVals': out of fuel"
    | fuel' + 1 =>
      match vs1, vs2 with
      | [],       []       => pure ()
      | v1 :: s1, v2 :: s2 => do
          eqVal' fuel' f k v1 v2
          eqVals' fuel' f k s1 s2
      | _,        _        => throwErrorMsg "mismatch number of arguments"
end

def eqVal (fuel : Nat) (k : Nat) (u1 u2 : Val) : TypeCheck Unit :=
  eqVal' fuel .N k u1 u2

mutual
  def leqVal' (fuel : Nat) (f : ForceHist) (k : Nat) (u1 u2 : Val) : TypeCheck Unit :=
    match fuel with
    | 0 => throwErrorMsg "leqVal': out of fuel"
    | fuel' + 1 => do
        let u1f ← force fuel' u1
        let u2f ← force fuel' u2
        if (u1f != u1) && !(u2f != u2) && (f != .R) then
          leqVal' fuel' .L k u1f u2
        else if !(u1f != u1) && (u2f != u2) && (f != .L) then
          leqVal' fuel' .R k u1 u2f
        else
          match u1, u2 with
          | .VSucc v1, .VSucc v2 => leqVal' fuel' f k v1 v2
          | .VApp v1 vl1, .VApp v2 vl2 => leqApp fuel' f k v1 vl1 v2 vl2
          | .VGen k1, .VGen k2 =>
              if k1 == k2 then pure ()
              else throwErrorMsg "gen mismatch"
          | .VPi x1 av1 env1 b1, .VPi x2 av2 env2 b2 => do
              leqVal' fuel' (switchForce f) k av2 av1
              let bv1 ← whnf fuel' (updateEnv env1 x1 (.VGen k)) b1
              let bv2 ← whnf fuel' (updateEnv env2 x2 (.VGen k)) b2
              leqVal' fuel' f (k + 1) bv1 bv2
          | .VLam x1 env1 e1, .VLam x2 env2 e2 => do
              let v1 ← whnf fuel' (updateEnv env1 x1 (.VGen k)) e1
              let v2 ← whnf fuel' (updateEnv env2 x2 (.VGen k)) e2
              leqVal' fuel' f (k + 1) v1 v2
          | a1, a2 =>
              if a1 == a2 then pure ()
              else throwErrorMsg "leqVal error"

  def leqVals' (fuel : Nat) (f : ForceHist) (k : Nat) (vs1 vs2 : List Val) : TypeCheck Unit :=
    match fuel with
    | 0 => throwErrorMsg "leqVals': out of fuel"
    | fuel' + 1 =>
      match vs1, vs2 with
      | [],       []       => pure ()
      | v1 :: s1, v2 :: s2 => do
          leqVal' fuel' f k v1 v2
          leqVals' fuel' f k s1 s2
      | _,        _        => throwErrorMsg "mismatch number of arguments"

  def leqApp (fuel : Nat) (f : ForceHist) (k : Nat) (v1 : Val) (w1 : List Val) (v2 : Val) (w2 : List Val) : TypeCheck Unit :=
    match fuel with
    | 0 => throwErrorMsg "leqApp: out of fuel"
    | fuel' + 1 =>
      match v1, v2 with
      | .VDef n, .VDef m =>
          if n == m then do
            let d ← lookupSig n
            match d with
            | .DataSig p pos s co _ => do
                let params1 := w1.take p
                let (pparams1, nparams1) := posArgs params1 pos
                let params2 := w2.take p
                let (pparams2, nparams2) := posArgs params2 pos
                leqVals' fuel' f k pparams1 pparams2
                let indices1 := w1.drop (p + 1)
                let indices2 := w2.drop (p + 1)
                eqVals' fuel' f k (nparams1 ++ indices1) (nparams2 ++ indices2)
                match getElemOpt w1 p, getElemOpt w2 p with
                | some idx1, some idx2 =>
                    match s with
                    | .Sized =>
                        match co with
                        | .Ind   => leqSize idx1 idx2
                        | .CoInd => leqSize idx2 idx1
                    | .NotSized => eqVal' fuel' f k idx1 idx2
                | _, _ => pure ()
            | _ => do
                leqVal' fuel' f k v1 v2
                eqVals' fuel' f k w1 w2
          else do
            leqVal' fuel' f k v1 v2
            eqVals' fuel' f k w1 w2
      | _, _ => do
          leqVal' fuel' f k v1 v2
          eqVals' fuel' f k w1 w2
end

def leqVal (fuel : Nat) (k : Nat) (u1 u2 : Val) : TypeCheck Unit :=
  leqVal' fuel .N k u1 u2

abbrev Substitution := List (Nat × TVal)
abbrev FlexEnv := List (Nat × (Expr × TVal))

def lookupSubst (k : Nat) : Substitution → Option TVal
  | []            => none
  | (j, v) :: rest => if k == j then some v else lookupSubst k rest

mutual
  def substVal (fuel : Nat) (sub : Substitution) (v : TVal) : TypeCheck Val :=
    match fuel with
    | 0 => throwErrorMsg "substVal: out of fuel"
    | fuel' + 1 =>
      match v with
      | .VGen k =>
          match lookupSubst k sub with
          | none    => pure v
          | some v' => pure v'
      | .VApp v1 vl => do
          let v1' ← substVal fuel' sub v1
          let vl' ← substValList fuel' sub vl
          app fuel' v1' vl'
      | .VSucc v1 => do
          let v1' ← substVal fuel' sub v1
          pure (sinfty v1')
      | .VPi x av env b => do
          let av' ← substVal fuel' sub av
          let env' ← substEnv fuel' sub env
          pure (.VPi x av' env' b)
      | .VLam x env b => do
          let env' ← substEnv fuel' sub env
          pure (.VLam x env' b)
      | _ => pure v

  def substValList (fuel : Nat) (sub : Substitution) (vs : List Val) : TypeCheck (List Val) :=
    match fuel with
    | 0 => throwErrorMsg "substValList: out of fuel"
    | fuel' + 1 =>
      match vs with
      | []        => pure []
      | v :: rest => do
          let v' ← substVal fuel' sub v
          let vs' ← substValList fuel' sub rest
          pure (v' :: vs')

  def substEnv (fuel : Nat) (sub : Substitution) (env : Env) : TypeCheck Env :=
    match fuel with
    | 0 => throwErrorMsg "substEnv: out of fuel"
    | fuel' + 1 =>
      match env with
      | []          => pure []
      | (x, v) :: e => do
          let v' ← substVal fuel' sub v
          let e' ← substEnv fuel' sub e
          pure ((x, v') :: e')
end

def compSubst (fuel : Nat) (s1 s2 : Substitution) : TypeCheck Substitution := do
  let s1' ← s1.mapM fun (k, v) => do
    let v' ← substVal fuel s2 v
    pure (k, v')
  pure (s1' ++ s2)

/- Pattern unification (`TypeChecker.hs` lines 564–595). -/
mutual
  def inst (fuel : Nat) (m : Nat) (flex : List Nat) (v1 v2 : Val) : TypeCheck Substitution :=
    match fuel with
    | 0 => throwErrorMsg "inst: out of fuel"
    | fuel' + 1 =>
      match v1, v2 with
      | .VGen k1, .VGen k2 =>
          if k1 == k2 then pure []
          else if flex.contains k1 then do
            let noc ← nocc fuel' m v1 v2
            if noc then pure [(k1, v2)] else throwErrorMsg "occurs check failed"
          else if flex.contains k2 then do
            let noc ← nocc fuel' m v2 v1
            if noc then pure [(k2, v1)] else throwErrorMsg "occurs check failed"
          else do
            eqVal fuel' m v1 v2
            pure []
      | .VGen k, _ =>
          if flex.contains k then do
            let noc ← nocc fuel' m v1 v2
            if noc then pure [(k, v2)] else throwErrorMsg "occurs check failed"
          else do
            eqVal fuel' m v1 v2
            pure []
      | _, .VGen k =>
          if flex.contains k then do
            let noc ← nocc fuel' m v2 v1
            if noc then pure [(k, v1)] else throwErrorMsg "occurs check failed"
          else do
            eqVal fuel' m v1 v2
            pure []
      | .VSucc v1', .VSucc v2' => inst fuel' m flex v1' v2'
      | .VSucc v, .VInfty      => inst fuel' m flex v .VInfty
      | .VApp (.VDef d1) vl1, .VApp (.VDef d2) vl2 =>
          if d1 == d2 then instList fuel' m flex vl1 vl2
          else do eqVal fuel' m v1 v2; pure []
      | .VApp (.VCon _ c1) vl1, .VApp (.VCon _ c2) vl2 =>
          if c1 == c2 then instList fuel' m flex vl1 vl2
          else do eqVal fuel' m v1 v2; pure []
      | _, _ => do
          eqVal fuel' m v1 v2
          pure []

  def instList (fuel : Nat) (m : Nat) (flex : List Nat) (vs1 vs2 : List Val) : TypeCheck Substitution :=
    match fuel with
    | 0 => throwErrorMsg "instList: out of fuel"
    | fuel' + 1 =>
      match vs1, vs2 with
      | [],        []        => pure []
      | v1 :: vl1, v2 :: vl2 => do
          let s ← inst fuel' m flex v1 v2
          let vl1' ← substValList fuel' s vl1
          let vl2' ← substValList fuel' s vl2
          let s' ← instList fuel' m flex vl1' vl2'
          compSubst fuel' s s'
      | _,         _         => throwErrorMsg "instList: length mismatch"
end

mutual
  def p2v (k : Nat) : Pattern → Val × Nat
    | .VarP _        => (.VGen k, k + 1)
    | .ConP co n []  => (.VCon co n, k)
    | .ConP co n pl  =>
        let (vl, k') := ps2vs k pl
        (.VApp (.VCon co n) vl, k')
    | .SuccP p       =>
        let (v, k') := p2v k p
        (.VSucc v, k')
    | .DotP _        => (.VGen k, k + 1)

  def ps2vs (k : Nat) : List Pattern → List Val × Nat
    | []      => ([], k)
    | p :: pl =>
        let (v, k') := p2v k p
        let (vl, k'') := ps2vs k' pl
        (v :: vl, k'')
end

def patternToVal (k : Nat) (p : Pattern) : Val :=
  (p2v k p).1

/-- Pattern-Refinement Invariant checks (`TypeChecker.hs` lines 546–561, Bug 1 fix). -/
def checkNoccEnv (fuel : Nat) (k : Nat) (j : Nat) : Env → TypeCheck Unit
  | []            => pure ()
  | (_, tv) :: env => do
      let b ← nocc fuel k (.VGen j) tv
      if b then checkNoccEnv fuel k j env
      else throwErrorMsg "unsound size refinement in pattern: size variable occurs in another pattern variable's type"

def checkNoccDomains (fuel : Nat) (k : Nat) (j : Nat) (tv : TVal) : TypeCheck Unit :=
  match fuel with
  | 0 => throwErrorMsg "checkNoccDomains: out of fuel"
  | fuel' + 1 =>
    match tv with
    | .VPi x av env b => do
        let ok ← nocc fuel' k (.VGen j) av
        if !ok then
          throwErrorMsg "unsound size refinement in pattern: size variable shared across multiple arguments or branches"
        else do
          let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
          checkNoccDomains fuel' (k + 1) j bv
    | _ => pure ()

def isNewSuccRefinement (ins ins'' : Substitution) (j : Nat) (tv : TVal) : Bool :=
  (tv == .VSize) &&
  (lookupSubst j ins == none) &&
  match lookupSubst j ins'' with
  | some (.VSucc _) => true
  | _               => false

/- Dependent pattern type-checking (`TypeChecker.hs` lines 421–498, with Bug 1 fix). -/
mutual
  def checkPattern (fuel : Nat) (k : Nat) (flex : FlexEnv) (ins : Substitution)
      (rho gamma : Env) (v : TVal) (p : Pattern)
      : TypeCheck (Nat × FlexEnv × Substitution × Env × Env × TVal) :=
    match fuel with
    | 0 => throwErrorMsg "checkPattern: out of fuel"
    | fuel' + 1 =>
      match v with
      | .VPi x av env b =>
          match p with
          | .VarP y => do
              let gk := Val.VGen k
              let bv ← whnf fuel' (updateEnv env x gk) b
              pure (k + 1, flex, ins, updateEnv rho y gk, updateEnv gamma y av, bv)
          | .ConP _ n pl => do
              let d ← lookupSig n
              match d with
              | .ConSig vc => do
                  let (k', flex', ins', rho', gamma', vc') ← checkPatterns fuel' k flex ins rho gamma vc pl
                  let flexgen := flex'.map Prod.fst
                  let sub ← inst fuel' k' flexgen vc' av
                  let pv := patternToVal k p
                  let vb0 ← whnf fuel' (updateEnv env x pv) b
                  let ins'' ← compSubst fuel' ins' sub
                  let newSuccVars := (flex'.filter fun (j, (_, tv)) => isNewSuccRefinement ins ins'' j tv).map Prod.fst
                  newSuccVars.forM fun j => do
                    checkNoccEnv fuel' k' j gamma
                    checkNoccDomains fuel' k' j vb0
                  let vb ← substVal fuel' ins'' vb0
                  let gamma'' ← substEnv fuel' ins'' gamma'
                  pure (k', flex', ins'', rho', gamma'', vb)
              | _ => throwErrorMsg ("Expected ConSig for " ++ n)
          | .SuccP p2 => do
              let st ← whnf fuel' [] (.Pi "" .Size .Size)
              let (k', flex', ins', rho', gamma', _) ← checkPattern fuel' k flex ins rho gamma st p2
              eqVal fuel' k' av .VSize
              let pv := patternToVal k p
              let vb ← whnf fuel' (updateEnv env x pv) b
              pure (k', flex', ins', rho', gamma', vb)
          | .DotP e => do
              let vb ← whnf fuel' (updateEnv env x (.VGen k)) b
              pure (k + 1, (k, (e, av)) :: flex, ins, rho, gamma, vb)
      | _ => throwErrorMsg "checkPattern: expected VPi"

  def checkPatterns (fuel : Nat) (k : Nat) (flex : FlexEnv) (ins : Substitution)
      (rho gamma : Env) (v : TVal) (pats : List Pattern)
      : TypeCheck (Nat × FlexEnv × Substitution × Env × Env × TVal) :=
    match fuel with
    | 0 => throwErrorMsg "checkPatterns: out of fuel"
    | fuel' + 1 =>
      match pats with
      | []      => pure (k, flex, ins, rho, gamma, v)
      | p :: pl => do
          let (k', flex', ins', rho', gamma', v') ← checkPattern fuel' k flex ins rho gamma v p
          checkPatterns fuel' k' flex' ins' rho' gamma' v' pl
end

/- Bidirectional expression type checking (`TypeChecker.hs` lines 328–397). -/
mutual
  def checkExpr (fuel : Nat) (k : Nat) (rho gamma : Env) (e : Expr) (v : TVal) : TypeCheck Unit :=
    match fuel with
    | 0 => throwErrorMsg "checkExpr: out of fuel"
    | fuel' + 1 =>
      match e, v with
      | .LLet n t1 e1 e2, _ => do
          checkType fuel' k rho gamma t1
          let v_t1 ← whnf fuel' rho t1
          checkExpr fuel' k rho gamma e1 v_t1
          let v_e1 ← whnf fuel' rho e1
          checkExpr fuel' k (updateEnv rho n v_e1) (updateEnv gamma n v_t1) e2 v
      | .Lam n e1, .VPi x va env t1 => do
          let v_t1 ← whnf fuel' (updateEnv env x (.VGen k)) t1
          checkExpr fuel' (k + 1) (updateEnv rho n (.VGen k)) (updateEnv gamma n va) e1 v_t1
      | .Pi n t1 t2, .VSet => do
          checkExpr fuel' k rho gamma t1 .VSet
          let v_t1 ← whnf fuel' rho t1
          checkExpr fuel' (k + 1) (updateEnv rho n (.VGen k)) (updateEnv gamma n v_t1) t2 .VSet
      | .Succ e2, .VSize =>
          checkExpr fuel' k rho gamma e2 .VSize
      | _, _ => do
          let v2 ← inferExpr fuel' k rho gamma e
          leqVal fuel' k v2 v

  def inferExpr (fuel : Nat) (k : Nat) (rho gamma : Env) (e : Expr) : TypeCheck TVal :=
    match fuel with
    | 0 => throwErrorMsg "inferExpr: out of fuel"
    | fuel' + 1 =>
      match e with
      | .Var x  => lookupEnv gamma x
      | .Infty  => pure .VSize
      | .App e1 [e2] => do
          let v ← inferExpr fuel' k rho gamma e1
          match v with
          | .VPi x av env b => do
              checkExpr fuel' k rho gamma e2 av
              let v2 ← whnf fuel' rho e2
              whnf fuel' (updateEnv env x v2) b
          | _ => throwErrorMsg "inferExpr: expected Pi"
      | .App e1 (e2 :: e3 :: el) =>
          inferExpr fuel' k rho gamma (.App (.App e1 [e2]) (e3 :: el))
      | .Def n => do
          let d ← lookupSig n
          match d with
          | .DataSig _ _ _ _ tv => pure tv
          | .FunSig _ tv _ _    => pure tv
          | _                   => throwErrorMsg ("Expected DataSig/FunSig for " ++ n)
      | .Con _ n => do
          let d ← lookupSig n
          match d with
          | .ConSig tv => pure tv
          | _          => throwErrorMsg ("Expected ConSig for " ++ n)
      | .Let n => do
          let d ← lookupSig n
          match d with
          | .LetSig tv _ => pure tv
          | _            => throwErrorMsg ("Expected LetSig for " ++ n)
      | _ => throwErrorMsg "cannot infer type"

  def checkType (fuel : Nat) (k : Nat) (rho gamma : Env) (e : Expr) : TypeCheck Unit :=
    match fuel with
    | 0 => throwErrorMsg "checkType: out of fuel"
    | fuel' + 1 =>
      match e with
      | .Set  => pure ()
      | .Size => pure ()
      | .Pi x t1 t2 => do
          checkType fuel' k rho gamma t1
          let v_t1 ← whnf fuel' rho t1
          checkType fuel' (k + 1) (updateEnv rho x (.VGen k)) (updateEnv gamma x v_t1) t2
      | _ => checkExpr fuel' k rho gamma e .VSet
end

def checkSType (fuel : Nat) (k : Nat) (rho gamma : Env) (e : Expr) : TypeCheck Unit :=
  tryCatch (checkExpr fuel k rho gamma e .VSet) (fun _ => throwErrorMsg ("not a set: " ++ prettyExpr e))

def checkT (fuel : Nat) (e : Expr) : TypeCheck Unit :=
  checkType fuel 0 [] [] e

def checkDot (fuel : Nat) (k : Nat) (rho gamma : Env) (sub : Substitution) : Nat × (Expr × TVal) → TypeCheck Unit
  | (i, (e, tv)) =>
      match lookupSubst i sub with
      | none   => throwErrorMsg "not instantiated"
      | some v => do
          let tv' ← substVal fuel sub tv
          checkExpr fuel k rho gamma e tv'
          let v' ← whnf fuel rho e
          eqVal fuel k v v'

def checkClause (fuel : Nat) (t : MType) : Clause → TypeCheck Unit
  | .mk pl rhs => do
      let v ← whnf fuel [] t
      let (k, flex, ins, rho, gamma, vt) ← checkPatterns fuel 0 [] [] [] [] v pl
      flex.forM (checkDot fuel k rho gamma ins)
      checkExpr fuel k rho gamma rhs vt

def checkFun (fuel : Nat) (t : MType) (cl : List Clause) : TypeCheck Unit :=
  cl.forM (checkClause fuel t)

/-- Sized data & function admissibility (`TypeChecker.hs` lines 643–841, including Bug 2 fix
    checking `nocc` on `rargs` in both `szSizeVarTarget` and `szUsed'`). -/
def doVParams (fuel : Nat) : Nat → Nat → TVal → TypeCheck (TVal × Nat)
  | 0,     k, tv              => pure (tv, k)
  | p + 1, k, .VPi x _ env b  => do
      let bv ← whnf fuel (updateEnv env x (.VGen k)) b
      doVParams fuel p (k + 1) bv
  | _,     _, _               => throwErrorMsg "doVParams: expected VPi"

def szType (fuel : Nat) (p : Nat) (tv : TVal) : TypeCheck Unit := do
  let (tv', _) ← doVParams fuel p 0 tv
  match tv' with
  | .VPi _ .VSize _ _ => pure ()
  | _                 => throwErrorMsg "not a sized type"

def szSizeVarTarget (fuel : Nat) (k : Nat) (p : Nat) (i : Nat) : TVal → TypeCheck Bool
  | .VApp _ vl =>
      match getElemOpt vl p with
      | some (.VSucc (.VGen i')) =>
          if i == i' then
            let rargs := vl.take p ++ vl.drop (p + 1)
            noccList fuel k (.VGen i) rargs
          else pure false
      | _ => pure false
  | _ => pure false

mutual
  def szSizeVarDataArgs (fuel : Nat) (n : Name) (k : Nat) (p : Nat) (i : Nat) (tv : TVal) : TypeCheck Bool :=
    match fuel with
    | 0 => throwErrorMsg "szSizeVarDataArgs: out of fuel"
    | fuel' + 1 =>
      match tv with
      | .VGen i'  => pure (i' != i)
      | .VSucc v' => szSizeVarDataArgs fuel' n k p i v'
      | .VApp (.VDef m) vl =>
          if n == m then
            match getElemOpt vl p with
            | some (.VGen i') =>
                if i' == i then
                  let rargs := vl.take p ++ vl.drop (p + 1)
                  noccList fuel' k (.VGen i) rargs
                else pure false
            | _ => pure false
          else do
            let b ← szSizeVarDataArgs fuel' n k p i (.VDef m)
            let bl ← szSizeVarDataArgsList fuel' n k p i vl
            pure (b && bl)
      | .VApp v1 vl => do
          let b ← szSizeVarDataArgs fuel' n k p i v1
          let bl ← szSizeVarDataArgsList fuel' n k p i vl
          pure (b && bl)
      | .VPi x av env b => do
          let k' := k + 1
          let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
          let b1 ← szSizeVarDataArgs fuel' n k' p i av
          let b2 ← szSizeVarDataArgs fuel' n k' p i bv
          pure (b1 && b2)
      | .VLam x env b => do
          let k' := k + 1
          let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
          szSizeVarDataArgs fuel' n k' p i bv
      | _ => pure true

  def szSizeVarDataArgsList (fuel : Nat) (n : Name) (k : Nat) (p : Nat) (i : Nat) (vs : List Val) : TypeCheck Bool :=
    match fuel with
    | 0 => throwErrorMsg "szSizeVarDataArgsList: out of fuel"
    | fuel' + 1 =>
      match vs with
      | []        => pure true
      | v :: rest => do
          let b1 ← szSizeVarDataArgs fuel' n k p i v
          let b2 ← szSizeVarDataArgsList fuel' n k p i rest
          pure (b1 && b2)
end

def szSizeVarUsage (fuel : Nat) (n : Name) (k : Nat) (p : Nat) (i : Nat) (tv : TVal) : TypeCheck Bool :=
  match fuel with
  | 0 => throwErrorMsg "szSizeVarUsage: out of fuel"
  | fuel' + 1 =>
    match tv with
    | .VPi x av env b => do
        let b1 ← szSizeVarDataArgs fuel' n k p i av
        let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
        let b2 ← szSizeVarUsage fuel' n (k + 1) p i bv
        pure (b1 && b2)
    | _ => szSizeVarTarget fuel' k p i tv

def szConstructor (fuel : Nat) (n : Name) (p : Nat) (tv : TVal) : TypeCheck Unit := do
  let (tv', k) ← doVParams fuel p 0 tv
  match tv' with
  | .VPi x .VSize env b => do
      let bv ← whnf fuel (updateEnv env x (.VGen k)) b
      let ok ← szSizeVarUsage fuel n (k + 1) p k bv
      if ok then pure () else throwErrorMsg "not a sized constructor"
  | _ => throwErrorMsg "not a sized constructor"

/-- Fixed `szUsed'` (`TypeChecker.hs` lines 826–841, Bug 2 fix checking `nocc` on `rargs`). -/
def szUsed' (fuel : Nat) (co : Co) (k : Nat) (i : Nat) : TVal → TypeCheck Bool
  | .VApp (.VDef n) vl => do
      let d ← lookupSig n
      match d with
      | .DataSig p _ .Sized co' _ =>
          if co == co' then
            match getElemOpt vl p with
            | some (.VGen i') =>
                if i == i' then
                  let rargs := vl.take p ++ vl.drop (p + 1)
                  noccList fuel k (.VGen i) rargs
                else pure false
            | _ => pure false
          else pure false
      | _ => pure false
  | _ => pure false

def szInductive (fuel : Nat) (k : Nat) (i : Nat) (tv : TVal) : TypeCheck Bool :=
  szUsed' fuel .Ind k i tv

def szCoInductive (fuel : Nat) (k : Nat) (i : Nat) (tv : TVal) : TypeCheck Bool :=
  szUsed' fuel .CoInd k i tv

def szMonotone (fuel : Nat) (k : Nat) (i : Nat) (tv : TVal) : TypeCheck Bool := do
  let si := Val.VSucc (.VGen i)
  let tv' ← substVal fuel [(i, si)] tv
  tryCatch (do leqVal fuel k tv tv'; pure true) (fun _ => pure false)

def szCheckIndFunSize (fuel : Nat) (k : Nat) (i : Nat) (tv : TVal) : TypeCheck Bool :=
  match fuel with
  | 0 => throwErrorMsg "szCheckIndFunSize: out of fuel"
  | fuel' + 1 =>
    match tv with
    | .VPi x av env b => do
        let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
        let k' := k + 1
        let ind ← szInductive fuel' k i av
        if ind then szCheckIndFunSize fuel' k' i bv
        else do
          let noc ← nocc fuel' k (.VGen i) av
          if noc then szCheckIndFunSize fuel' k' i bv
          else pure false
    | _ => szMonotone fuel' k i tv

def szCheckIndFun (fuel : Nat) (k : Nat) (tv : TVal) : TypeCheck Bool :=
  match fuel with
  | 0 => throwErrorMsg "szCheckIndFun: out of fuel"
  | fuel' + 1 =>
    match tv with
    | .VPi x av env b => do
        let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
        let k' := k + 1
        match av with
        | .VSize => do
            let ok ← szCheckIndFunSize fuel' k' k bv
            if ok then szCheckIndFun fuel' k' bv else pure false
        | _ => szCheckIndFun fuel' k' bv
    | _ => pure true

def szCheckCoFunSize (fuel : Nat) (k : Nat) (i : Nat) (tv : TVal) : TypeCheck Bool :=
  match fuel with
  | 0 => throwErrorMsg "szCheckCoFunSize: out of fuel"
  | fuel' + 1 =>
    match tv with
    | .VPi x av env b => do
        let noc ← nocc fuel' k (.VGen i) av
        if noc then do
          let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
          szCheckCoFunSize fuel' (k + 1) i bv
        else pure false
    | _ => szCoInductive fuel' k i tv

def szCheckCoFun (fuel : Nat) (k : Nat) (tv : TVal) : TypeCheck Bool :=
  match fuel with
  | 0 => throwErrorMsg "szCheckCoFun: out of fuel"
  | fuel' + 1 =>
    match tv with
    | .VPi x av env b => do
        let bv ← whnf fuel' (updateEnv env x (.VGen k)) b
        let k' := k + 1
        match av with
        | .VSize => do
            let ok ← szCheckCoFunSize fuel' k' k bv
            if ok then szCheckCoFun fuel' k' bv else pure false
        | _ => szCheckCoFun fuel' k' bv
    | .VApp (.VDef n) _ => do
        let d ← lookupSig n
        match d with
        | .DataSig _ _ _ .CoInd _ => pure true
        | _ => throwErrorMsg "cofun doesn't target coinductive type"
    | .VDef n => do
        let d ← lookupSig n
        match d with
        | .DataSig _ _ _ .CoInd _ => pure true
        | _ => throwErrorMsg "cofun doesn't target coinductive type"
    | _ => throwErrorMsg "cofun doesn't target coinductive type"

def checkDataType (fuel : Nat) (k : Nat) (rho gamma : Env) (p : Nat) : Expr → TypeCheck Unit
  | .Pi x t1 t2 => do
      if k < p then checkType fuel k rho gamma t1
      else checkSType fuel k rho gamma t1
      let v_t1 ← whnf fuel rho t1
      checkDataType fuel (k + 1) (updateEnv rho x (.VGen k)) (updateEnv gamma x v_t1) p t2
  | .Set => pure ()
  | _    => throwErrorMsg "doesn't target Set"

def checkConType (fuel : Nat) (k : Nat) (rho gamma : Env) (p : Nat) : Expr → TypeCheck Unit
  | .Pi x t1 t2 => do
      if k < p then pure ()
      else checkSType fuel k rho gamma t1
      let v_t1 ← whnf fuel rho t1
      checkConType fuel (k + 1) (updateEnv rho x (.VGen k)) (updateEnv gamma x v_t1) p t2
  | e => checkExpr fuel k rho gamma e .VSet

def checkPs : Telescope → List Expr → TypeCheck Unit
  | [],          []             => pure ()
  | (n, _) :: tl, .Var n' :: el =>
      if n == n' then checkPs tl el else throwErrorMsg "target param mismatch"
  | _,           _              => throwErrorMsg "target param mismatch"

def checkTarget (d : Name) (tel : Telescope) : MType → TypeCheck Unit
  | .App (.Def n) al =>
      if n == d then checkPs tel (al.take tel.length)
      else throwErrorMsg "target mismatch"
  | .Def n =>
      if n == d && tel.isEmpty then pure ()
      else throwErrorMsg "target mismatch"
  | _ => throwErrorMsg "target mismatch"

def typeCheckConstructor (fuel : Nat) (d : Name) (sz : Sized) (pos : List Pos) (tel : Telescope) : Constructor → TypeCheck Unit
  | .mk n t => throwTrace (do
      let tt := teleToType tel t
      let params := tel.length
      let p' := match sz with | .Sized => params + 1 | .NotSized => params
      checkConType fuel 0 [] [] p' tt
      let (_, target) := typeToTele tt
      checkTarget d tel target
      let vt ← whnf fuel [] tt
      sposConstructor fuel d 0 pos vt
      let sig ← getSig
      putSig (addSig sig n (.ConSig vt))
      match sz with
      | .Sized    => szConstructor fuel d params vt
      | .NotSized => pure ()
    ) n

def typeCheckFuns (fuel : Nat) (co : Co) (funs : List (TypeSig × List Clause)) : TypeCheck Unit := do
  -- 1. Register unverified function signatures
  funs.forM fun (.mk n t, cl) => do
    let sig ← getSig
    let vt ← whnf fuel [] t
    putSig (addSig sig n (.FunSig co vt cl false))
  -- 2. Check admissibility & size-pattern completeness
  let adms ← funs.mapM fun (.mk n t, cl) => throwTrace (do
    checkT fuel t
    let vt ← whnf fuel [] t
    let adm ← match co with
      | .Ind   => szCheckIndFun fuel 0 vt
      | .CoInd => szCheckCoFun fuel 0 vt
    let b := match co with
      | .Ind   => completePatterns cl
      | .CoInd => true
    if !adm then addWarning (n ++ " : type not admissible")
    if !b then addWarning (n ++ " : size pattern incomplete")
    pure (adm && b)
  ) ("type of " ++ n)
  -- 3. Type-check all clauses
  funs.forM fun (.mk n t, cl) => throwTrace (checkFun fuel t cl) n
  -- 4. Run Size-Change Termination check
  let termOk := terminationCheck funs
  if !termOk then addWarning "Termination check fails"
  if adms.all id && termOk then
    funs.forM fun (.mk n _, _) => do
      let d ← lookupSig n
      match d with
      | .FunSig c vt cl _ => do
          let sig ← getSig
          putSig (addSig sig n (.FunSig c vt cl true))
      | _ => pure ()

def typeCheckDeclaration (fuel : Nat) : Declaration → TypeCheck Unit
  | .DataDecl n sz co pos tel t cs => throwTrace (do
      let dt := teleToType tel t
      let params := tel.length
      let p' := match sz with | .Sized => params + 1 | .NotSized => params
      checkDataType fuel 0 [] [] p' dt
      let v ← whnf fuel [] dt
      let sig ← getSig
      putSig (addSig sig n (.DataSig params pos sz co v))
      match sz with
      | .Sized    => szType fuel params v
      | .NotSized => pure ()
      cs.forM (typeCheckConstructor fuel n sz pos tel)
    ) n
  | .LetDecl _ (.mk n t) e => throwTrace (do
      checkT fuel t
      let vt ← whnf fuel [] t
      checkExpr fuel 0 [] [] e vt
      let sig ← getSig
      putSig (addSig sig n (.LetSig vt e))
    ) n
  | .FunDecl co funs => typeCheckFuns fuel co funs

def typeCheckDecls (fuel : Nat) (dl : List Declaration) : TypeCheck Unit :=
  dl.forM (typeCheckDeclaration fuel)

def checkProgram (dl : List Declaration) : Except String TCState :=
  match runTypeCheck {} (typeCheckDecls defaultFuel dl) with
  | .ok (_, st) =>
      if st.warnings.isEmpty then .ok st
      else .error (String.intercalate "; " st.warnings)
  | .error msg => .error msg

/-! ## 7. Port of `Concrete.hs`, `ScopeChecker.hs`, `Lexer.hs` & `Parser.hs` -/

/-! ### 7.1 Concrete Syntax (`Concrete.hs`) -/

inductive CExpr : Type where
  | Set   : CExpr
  | Size  : CExpr
  | Succ  : CExpr → CExpr
  | Infty : CExpr
  | App   : CExpr → List CExpr → CExpr
  | Lam   : Name → CExpr → CExpr
  | LLet  : Name → CExpr → CExpr → CExpr → CExpr
  | Pi    : Name → CExpr → CExpr → CExpr
  | Ident : Name → CExpr
  deriving Repr, Inhabited, BEq

inductive CTBind : Type where
  | TB    : Name → CExpr → CTBind
  | PosTB : Name → CExpr → CTBind
  deriving Repr, Inhabited, BEq

abbrev CTelescope := List CTBind

inductive CTypeSig : Type where
  | mk : Name → CExpr → CTypeSig
  deriving Repr, Inhabited, BEq

inductive CPattern : Type where
  | ConP   : Name → List CPattern → CPattern
  | SuccP  : CPattern → CPattern
  | DotP   : CExpr → CPattern
  | IdentP : Name → CPattern
  deriving Repr, Inhabited, BEq

inductive CClause : Type where
  | mk : List CPattern → CExpr → CClause
  deriving Repr, Inhabited, BEq

inductive CDeclaration : Type where
  | DataDecl   : Name → Sized → Co → CTelescope → CExpr → List CTypeSig → CDeclaration
  | FunDecl    : Co → CTypeSig → List CClause → CDeclaration
  | LetDecl    : Bool → CTypeSig → CExpr → CDeclaration
  | MutualDecl : List CDeclaration → CDeclaration
  deriving Repr, Inhabited, BEq

def cTeleToType : CTelescope → CExpr → CExpr
  | [],                 t2 => t2
  | .TB n t :: tel,     t2 => .Pi n t (cTeleToType tel t2)
  | .PosTB n t :: tel,  t2 => .Pi n t (cTeleToType tel t2)

/-! ### 7.2 Scope Checker (`ScopeChecker.hs`) -/

inductive IKind : Type where
  | DataK : IKind
  | ConK  : Co → IKind
  | FunK  : IKind
  | LetK  : IKind
  deriving Repr, Inhabited, BEq

abbrev ScopeCtx := List Name
abbrev ScopeSig := List (Name × IKind)

def lookupScopeSig (n : Name) : ScopeSig → Option IKind
  | []            => none
  | (x, k) :: xs  => if x == n then some k else lookupScopeSig n xs

def addScopeSig (n : Name) (k : IKind) (sig : ScopeSig) : ScopeSig :=
  sig ++ [(n, k)]

abbrev ScopeCheck (α : Type) := ReaderT ScopeCtx (StateT ScopeSig (Except String)) α

def runScopeCheck (ctx : ScopeCtx) (sig : ScopeSig) (m : ScopeCheck α) : Except String (α × ScopeSig) :=
  StateT.run (ReaderT.run m ctx) sig

def posTelescope : CTelescope → List Pos
  | []                => []
  | .TB _ _ :: tel    => .NSPos :: posTelescope tel
  | .PosTB _ _ :: tel => .SPos :: posTelescope tel

def collectTelescopeNames : CTelescope → List Name
  | []                => []
  | .TB n _ :: tel    => n :: collectTelescopeNames tel
  | .PosTB n _ :: tel => n :: collectTelescopeNames tel

mutual
  def scopeCheckExpr : CExpr → ScopeCheck Expr
    | .Set      => pure .Set
    | .Size     => pure .Size
    | .Succ e1  => do
        let e1' ← scopeCheckExpr e1
        pure (.Succ e1')
    | .Infty    => pure .Infty
    | .App e1 el => do
        let e1' ← scopeCheckExpr e1
        let el' ← scopeCheckExprList el
        pure (.App e1' el')
    | .Pi "" t e1 => do
        let t' ← scopeCheckExpr t
        let e1' ← scopeCheckExpr e1
        pure (.Pi "" t' e1')
    | .Pi n t e1 => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some _ => throw ("Identifier " ++ n ++ " already in signature")
        | none   =>
            if ctx.contains n then throw ("Identifier " ++ n ++ " already in context")
            else do
              let t' ← scopeCheckExpr t
              let e1' ← withReader (fun c => c ++ [n]) (scopeCheckExpr e1)
              pure (.Pi n t' e1')
    | .Lam n e1 => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some _ => throw ("Identifier " ++ n ++ " already in signature")
        | none   =>
            if ctx.contains n then throw ("Identifier " ++ n ++ " already in context")
            else do
              let e1' ← withReader (fun c => c ++ [n]) (scopeCheckExpr e1)
              pure (.Lam n e1')
    | .LLet n t1 e1 e2 => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some _ => throw ("Identifier " ++ n ++ " already in signature")
        | none   =>
            if ctx.contains n then throw ("Identifier " ++ n ++ " already in context")
            else do
              let t1' ← scopeCheckExpr t1
              let e1' ← scopeCheckExpr e1
              let e2' ← withReader (fun c => c ++ [n]) (scopeCheckExpr e2)
              pure (.LLet n t1' e1' e2')
    | .Ident n => do
        let ctx ← read
        let sig ← get
        match lookupScopeSig n sig with
        | some (.ConK co) => pure (.Con co n)
        | some .LetK      => pure (.Let n)
        | some _          => pure (.Def n)
        | none            =>
            if ctx.contains n then pure (.Var n)
            else throw ("Identifier " ++ n ++ " undefined")

  def scopeCheckExprList : List CExpr → ScopeCheck (List Expr)
    | []      => pure []
    | e :: es => do
        let e' ← scopeCheckExpr e
        let es' ← scopeCheckExprList es
        pure (e' :: es')
end

def scopeCheckTypeSig : CTypeSig → ScopeCheck TypeSig
  | .mk n t => do
      let sig ← get
      match lookupScopeSig n sig with
      | some _ => throw ("Identifier " ++ n ++ " already in signature")
      | none   => do
          let t' ← scopeCheckExpr t
          pure (.mk n t')

def scopeCheckConstructor (co : Co) : CTypeSig → ScopeCheck Constructor
  | .mk n t => do
      let sig ← get
      match lookupScopeSig n sig with
      | some _ => throw ("Identifier " ++ n ++ " already in signature")
      | none   => do
          let t' ← scopeCheckExpr t
          set (addScopeSig n (.ConK co) sig)
          pure (.mk n t')

mutual
  def scopeCheckPattern : CPattern → ScopeCheck Pattern
    | .IdentP n => do
        let sig ← get
        match lookupScopeSig n sig with
        | some (.ConK co) => pure (.ConP co n [])
        | some _          => throw ("pattern " ++ n ++ " not a constructor")
        | none            => pure (.VarP n)
    | .SuccP p2 => do
        let p2' ← scopeCheckPattern p2
        pure (.SuccP p2')
    | .ConP n pl => do
        let sig ← get
        match lookupScopeSig n sig with
        | some (.ConK co) => do
            let pl' ← scopeCheckPatternList pl
            pure (.ConP co n pl')
        | _ => throw ("pattern " ++ n ++ " not a constructor")
    | .DotP _ => pure (.VarP "")

  def scopeCheckPatternList : List CPattern → ScopeCheck (List Pattern)
    | []      => pure []
    | p :: ps => do
        let p' ← scopeCheckPattern p
        let ps' ← scopeCheckPatternList ps
        pure (p' :: ps')
end

mutual
  def scopeCheckDotPattern : CPattern → Pattern → ScopeCheck Pattern
    | .DotP e, _ => do
        let e' ← scopeCheckExpr e
        pure (.DotP e')
    | .SuccP p1', .SuccP p2' => do
        let p2'' ← scopeCheckDotPattern p1' p2'
        pure (.SuccP p2'')
    | .ConP _ pl, .ConP co n pl' => do
        let pl'' ← scopeCheckDotPatternList pl pl'
        pure (.ConP co n pl'')
    | _, p2 => pure p2

  def scopeCheckDotPatternList : List CPattern → List Pattern → ScopeCheck (List Pattern)
    | [],      _       => pure []
    | _,       []      => pure []
    | c :: cs, p :: ps => do
        let p' ← scopeCheckDotPattern c p
        let ps' ← scopeCheckDotPatternList cs ps
        pure (p' :: ps')
end

def collectVarPNamesAux : Nat → List Pattern → List Name → ScopeCheck (List Name)
  | 0,        _,                  acc => pure acc
  | _ + 1,    [],                 acc => pure acc
  | fuel + 1, .SuccP p2 :: pl,    acc => collectVarPNamesAux fuel (p2 :: pl) acc
  | fuel + 1, .ConP _ _ pl2 :: pl, acc => collectVarPNamesAux fuel (pl2 ++ pl) acc
  | fuel + 1, .VarP "" :: pl,     acc => collectVarPNamesAux fuel pl acc
  | fuel + 1, .VarP n :: pl,      acc =>
      if acc.contains n then throw ("pattern not linear: " ++ n)
      else collectVarPNamesAux fuel pl (n :: acc)
  | fuel + 1, .DotP _ :: pl,      acc => collectVarPNamesAux fuel pl acc

def collectVarPNames (pl : List Pattern) : ScopeCheck (List Name) :=
  collectVarPNamesAux 1000 pl []

def scopeCheckClause : CClause → ScopeCheck Clause
  | .mk pl rhs => do
      let pl' ← scopeCheckPatternList pl
      let names ← collectVarPNames pl'
      let pl'' ← withReader (fun c => c ++ names) (scopeCheckDotPatternList pl pl')
      let rhs' ← withReader (fun c => c ++ names) (scopeCheckExpr rhs)
      pure (.mk pl'' rhs')

def checkPatternLength : List CClause → Bool
  | []             => true
  | .mk pl _ :: cl => cl.all fun (.mk pl2 _) => pl2.length == pl.length

def scopeCheckFunDecls (co : Co) (decls : List CDeclaration) : ScopeCheck Declaration := do
  -- 1. Check signatures
  let tsl' ← decls.mapM fun d =>
    match d with
    | .FunDecl co' ts _ =>
        if co == co' then scopeCheckTypeSig ts
        else throw "mutual combination not supported"
    | _ => throw "mutual combination not supported"
  -- 2. Add function names to scope signature
  decls.forM fun d =>
    match d with
    | .FunDecl _ (.mk n _) _ => modify (addScopeSig n .FunK)
    | _ => pure ()
  -- 3. Check clauses
  let cll' ← decls.mapM fun d =>
    match d with
    | .FunDecl _ (.mk _ _) cl => do
        let cl' ← cl.mapM scopeCheckClause
        if checkPatternLength cl then pure cl'
        else throw "pattern length differs"
    | _ => throw "mutual combination not supported"
  pure (.FunDecl co (tsl'.zip cll'))

def scopeCheckDeclaration : CDeclaration → ScopeCheck Declaration
  | .DataDecl n sz co tel t cs => do
      let pos := posTelescope tel
      let tt := cTeleToType tel t
      let .mk _ tt' ← scopeCheckTypeSig (.mk n tt)
      let (tel', t') := splitTeleType tel.length ([], tt')
      modify (addScopeSig n .DataK)
      let names := collectTelescopeNames tel
      let cs' ← withReader (fun c => c ++ names) (cs.mapM (scopeCheckConstructor co))
      pure (.DataDecl n sz co pos tel' t' cs')
  | d@(.FunDecl co _ _) => scopeCheckFunDecls co [d]
  | .LetDecl b ts@(.mk n _) e => do
      let e' ← scopeCheckExpr e
      let ts' ← scopeCheckTypeSig ts
      modify (addScopeSig n .LetK)
      pure (.LetDecl b ts' e')
  | .MutualDecl (.FunDecl co ts cl :: rest) =>
      scopeCheckFunDecls co (.FunDecl co ts cl :: rest)
  | .MutualDecl _ => throw "mutual combination not supported"

def scopeCheck (dl : List CDeclaration) : Except String (List Declaration) :=
  match runScopeCheck [] [] (dl.mapM scopeCheckDeclaration) with
  | .ok (decls, _) => .ok decls
  | .error err     => .error err

/-! ### 7.3 Lexer & Recursive-Descent Parser (`Lexer.hs` & `Parser.hs`) -/

inductive Token : Type where
  | Id      : String → Token
  | Sized   : Token
  | Data    : Token
  | CoData  : Token
  | Mutual  : Token
  | Fun     : Token
  | CoFun   : Token
  | Let     : Token
  | In      : Token
  | Set     : Token
  | Eval    : Token
  | Size    : Token
  | Infty   : Token
  | Succ    : Token
  | BrOpen  : Token
  | BrClose : Token
  | PrOpen  : Token
  | PrClose : Token
  | Sem     : Token
  | Col     : Token
  | Dot     : Token
  | Arrow   : Token
  | Eq      : Token
  | Plus    : Token
  | Lam     : Token
  deriving Repr, Inhabited, BEq

def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\''

def classifyIdent : String → Token
  | "sized"  => .Sized
  | "data"   => .Data
  | "codata" => .CoData
  | "fun"    => .Fun
  | "cofun"  => .CoFun
  | "let"    => .Let
  | "const"  => .Let
  | "in"     => .In
  | "eval"   => .Eval
  | "mutual" => .Mutual
  | "Set"    => .Set
  | "Size"   => .Size
  | s        => .Id s

def dropLineComment : List Char → List Char
  | []          => []
  | '\n' :: cs  => cs
  | _ :: cs     => dropLineComment cs

def dropBlockComment : Nat → List Char → Except String (List Char)
  | 0,        _                 => .error "Lexer: out of fuel in block comment"
  | _,        []                => .error "Unterminated block comment"
  | _ + 1,    '-' :: '}' :: cs  => .ok cs
  | fuel + 1, _ :: cs           => dropBlockComment fuel cs

def takeIdentChars : List Char → List Char × List Char
  | []      => ([], [])
  | c :: cs =>
      if isIdentChar c then
        let (idChars, rest) := takeIdentChars cs
        (c :: idChars, rest)
      else ([], c :: cs)

def scanTokensAux : Nat → List Char → Except String (List Token)
  | 0,        _                 => .error "Lexer: out of fuel"
  | _,        []                => .ok []
  | fuel + 1, '-' :: '-' :: cs  => scanTokensAux fuel (dropLineComment cs)
  | fuel + 1, '{' :: '-' :: cs  => do
      let rest ← dropBlockComment fuel cs
      scanTokensAux fuel rest
  | fuel + 1, '-' :: '>' :: cs  => do
      let toks ← scanTokensAux fuel cs
      .ok (.Arrow :: toks)
  | fuel + 1, c :: cs =>
      if c.isWhitespace then scanTokensAux fuel cs
      else match c with
      | '#'  => (.Infty :: ·)   <$> scanTokensAux fuel cs
      | '$'  => (.Succ :: ·)    <$> scanTokensAux fuel cs
      | '{'  => (.BrOpen :: ·)  <$> scanTokensAux fuel cs
      | '}'  => (.BrClose :: ·) <$> scanTokensAux fuel cs
      | '('  => (.PrOpen :: ·)  <$> scanTokensAux fuel cs
      | ')'  => (.PrClose :: ·) <$> scanTokensAux fuel cs
      | ';'  => (.Sem :: ·)     <$> scanTokensAux fuel cs
      | ':'  => (.Col :: ·)     <$> scanTokensAux fuel cs
      | '.'  => (.Dot :: ·)     <$> scanTokensAux fuel cs
      | '+'  => (.Plus :: ·)    <$> scanTokensAux fuel cs
      | '='  => (.Eq :: ·)      <$> scanTokensAux fuel cs
      | '\\' => (.Lam :: ·)     <$> scanTokensAux fuel cs
      | _    =>
          if isIdentChar c then
            let (idRest, rest) := takeIdentChars cs
            let ident := String.ofList (c :: idRest)
            (classifyIdent ident :: ·) <$> scanTokensAux fuel rest
          else .error ("Unexpected character: " ++ String.ofList [c])

def tokenize (s : String) : Except String (List Token) :=
  let chars := s.toList
  scanTokensAux (chars.length + 10) chars

def startsExpr3 : List Token → Bool
  | .Set :: _    => true
  | .Size :: _   => true
  | .Infty :: _  => true
  | .Id _ :: _   => true
  | .PrOpen :: _ => true
  | _            => false

def expectTok (expected : Token) : List Token → Except String (List Token)
  | t :: ts => if t == expected then .ok ts else .error ("Unexpected token, expected " ++ reprStr expected)
  | []      => .error ("Unexpected EOF, expected " ++ reprStr expected)

mutual
  def parseExpr (fuel : Nat) (ts : List Token) : Except String (CExpr × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .Lam :: .Id x :: .Arrow :: rest => do
          let (e, ts1) ← parseExpr fuel' rest
          .ok (.Lam x e, ts1)
      | .Let :: .Id x :: .Col :: rest => do
          let (ty, ts1) ← parseExpr fuel' rest
          let ts2 ← expectTok .Eq ts1
          let (e1, ts3) ← parseExpr fuel' ts2
          let ts4 ← expectTok .In ts3
          let (e2, ts5) ← parseExpr fuel' ts4
          .ok (.LLet x ty e1 e2, ts5)
      | .PrOpen :: .Id x :: .Col :: rest =>
          match parseExpr fuel' rest with
          | .ok (ty, .PrClose :: .Arrow :: tsAfter) => do
              let (body, ts1) ← parseExpr fuel' tsAfter
              .ok (.Pi x ty body, ts1)
          | _ => parseExprArrow fuel' ts
      | _ => parseExprArrow fuel' ts

  def parseExprArrow (fuel : Nat) (ts : List Token) : Except String (CExpr × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 => do
        let (e1, ts1) ← parseExpr1 fuel' ts
        match ts1 with
        | .Arrow :: ts2 => do
            let (e2, ts3) ← parseExpr fuel' ts2
            .ok (.Pi "" e1 e2, ts3)
        | _ => .ok (e1, ts1)

  def parseExpr1 (fuel : Nat) (ts : List Token) : Except String (CExpr × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 => do
        let (es, ts1) ← parseExpr2 fuel' ts
        match es with
        | [e]     => .ok (e, ts1)
        | e :: el => .ok (.App e el, ts1)
        | []      => .error "Parse error: empty expression"

  def parseExpr2 (fuel : Nat) (ts : List Token) : Except String (List CExpr × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .Succ :: rest => do
          let (se, ts1) ← parseSE fuel' rest
          let (more, ts2) ← parseExpr3Many fuel' ts1
          .ok (.Succ se :: more, ts2)
      | _ => do
          let (e, ts1) ← parseExpr3 fuel' ts
          let (more, ts2) ← parseExpr3Many fuel' ts1
          .ok (e :: more, ts2)

  def parseSE (fuel : Nat) (ts : List Token) : Except String (CExpr × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .Succ :: rest => do
          let (se, ts1) ← parseSE fuel' rest
          .ok (.Succ se, ts1)
      | _ => parseExpr3 fuel' ts

  def parseExpr3Many (fuel : Nat) (ts : List Token) : Except String (List CExpr × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      if startsExpr3 ts then do
        let (e, ts1) ← parseExpr3 fuel' ts
        let (es, ts2) ← parseExpr3Many fuel' ts1
        .ok (e :: es, ts2)
      else .ok ([], ts)

  def parseExpr3 (fuel : Nat) (ts : List Token) : Except String (CExpr × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .Set :: rest   => .ok (.Set, rest)
      | .Size :: rest  => .ok (.Size, rest)
      | .Infty :: rest => .ok (.Infty, rest)
      | .Id x :: rest  => .ok (.Ident x, rest)
      | .PrOpen :: rest => do
          let (e, ts1) ← parseExpr fuel' rest
          let ts2 ← expectTok .PrClose ts1
          .ok (e, ts2)
      | _ => .error "Parse error in atomic expression"
end

mutual
  def parsePattern (fuel : Nat) (ts : List Token) : Except String (CPattern × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .PrOpen :: .Succ :: rest => do
          let (sp, ts1) ← parseSP fuel' rest
          let ts2 ← expectTok .PrClose ts1
          .ok (.SuccP sp, ts2)
      | .PrOpen :: .Id c :: rest => do
          let (ps, ts1) ← parsePatternsUntilEq fuel' rest
          let ts2 ← expectTok .PrClose ts1
          .ok (.ConP c ps, ts2)
      | .Id x :: rest => .ok (.IdentP x, rest)
      | .Dot :: rest => do
          let (e, ts1) ← parseExpr3 fuel' rest
          .ok (.DotP e, ts1)
      | _ => .error "Parse error in pattern"

  def parseSP (fuel : Nat) (ts : List Token) : Except String (CPattern × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .Succ :: rest => do
          let (sp, ts1) ← parseSP fuel' rest
          .ok (.SuccP sp, ts1)
      | _ => parsePattern fuel' ts

  def parsePatternsUntilEq (fuel : Nat) (ts : List Token) : Except String (List CPattern × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .Eq :: _      => .ok ([], ts)
      | .PrClose :: _ => .ok ([], ts)
      | _ => do
          let (p, ts1) ← parsePattern fuel' ts
          let (ps, ts2) ← parsePatternsUntilEq fuel' ts1
          .ok (p :: ps, ts2)
end

def parseTypeSig (fuel : Nat) : List Token → Except String (CTypeSig × List Token)
  | .Id name :: .Col :: ts => do
      let (ty, ts1) ← parseExpr fuel ts
      .ok (.mk name ty, ts1)
  | _ => .error "Parse error in type signature"

def parseDataTelescope (fuel : Nat) (ts : List Token) : Except String (CTelescope × List Token) :=
  match fuel with
  | 0 => .error "Parser: out of fuel"
  | fuel' + 1 =>
    match ts with
    | .PrOpen :: .Plus :: .Id x :: .Col :: rest => do
        let (ty, ts1) ← parseExpr fuel' rest
        let ts2 ← expectTok .PrClose ts1
        let (tel, ts3) ← parseDataTelescope fuel' ts2
        .ok (.PosTB x ty :: tel, ts3)
    | .PrOpen :: .Id x :: .Col :: rest => do
        let (ty, ts1) ← parseExpr fuel' rest
        let ts2 ← expectTok .PrClose ts1
        let (tel, ts3) ← parseDataTelescope fuel' ts2
        .ok (.TB x ty :: tel, ts3)
    | _ => .ok ([], ts)

def parseConstructors (fuel : Nat) (ts : List Token) : Except String (List CTypeSig × List Token) :=
  match fuel with
  | 0 => .error "Parser: out of fuel"
  | fuel' + 1 =>
    match ts with
    | .BrClose :: _ => .ok ([], ts)
    | _ => do
        let (c, ts1) ← parseTypeSig fuel' ts
        match ts1 with
        | .Sem :: ts2 => do
            let (cs, ts3) ← parseConstructors fuel' ts2
            .ok (c :: cs, ts3)
        | _ => .ok ([c], ts1)

def parseClause (fuel : Nat) : List Token → Except String (CClause × List Token)
  | .Id _ :: ts => do
      let (ps, ts1) ← parsePatternsUntilEq fuel ts
      let ts2 ← expectTok .Eq ts1
      let (rhs, ts3) ← parseExpr fuel ts2
      .ok (.mk ps rhs, ts3)
  | _ => .error "Parse error in clause"

def parseClauses (fuel : Nat) (ts : List Token) : Except String (List CClause × List Token) :=
  match fuel with
  | 0 => .error "Parser: out of fuel"
  | fuel' + 1 =>
    match ts with
    | .BrClose :: _ => .ok ([], ts)
    | _ => do
        let (c, ts1) ← parseClause fuel' ts
        match ts1 with
        | .Sem :: ts2 => do
            let (cs, ts3) ← parseClauses fuel' ts2
            .ok (c :: cs, ts3)
        | _ => .ok ([c], ts1)

def parseDataRest (fuel : Nat) (name : Name) (sz : Sized) (co : Co) (ts : List Token)
    : Except String (CDeclaration × List Token) := do
  let (tel, ts1) ← parseDataTelescope fuel ts
  let ts2 ← expectTok .Col ts1
  let (ty, ts3) ← parseExpr fuel ts2
  let ts4 ← expectTok .BrOpen ts3
  let (cs, ts5) ← parseConstructors fuel ts4
  let ts6 ← expectTok .BrClose ts5
  .ok (.DataDecl name sz co tel ty cs, ts6)

mutual
  def parseDeclaration (fuel : Nat) (ts : List Token) : Except String (CDeclaration × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | .Data :: .Id name :: rest => parseDataRest fuel' name .NotSized .Ind rest
      | .Sized :: .Data :: .Id name :: rest => parseDataRest fuel' name .Sized .Ind rest
      | .CoData :: .Id name :: rest => parseDataRest fuel' name .NotSized .CoInd rest
      | .Sized :: .CoData :: .Id name :: rest => parseDataRest fuel' name .Sized .CoInd rest
      | .Fun :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .BrOpen ts1
          let (cls, ts3) ← parseClauses fuel' ts2
          let ts4 ← expectTok .BrClose ts3
          .ok (.FunDecl .Ind tsig cls, ts4)
      | .CoFun :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .BrOpen ts1
          let (cls, ts3) ← parseClauses fuel' ts2
          let ts4 ← expectTok .BrClose ts3
          .ok (.FunDecl .CoInd tsig cls, ts4)
      | .Mutual :: .BrOpen :: rest => do
          let (decls, ts1) ← parseDeclarations fuel' rest
          let ts2 ← expectTok .BrClose ts1
          .ok (.MutualDecl decls, ts2)
      | .Let :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .Eq ts1
          let (e, ts3) ← parseExpr fuel' ts2
          .ok (.LetDecl false tsig e, ts3)
      | .Eval :: .Let :: rest => do
          let (tsig, ts1) ← parseTypeSig fuel' rest
          let ts2 ← expectTok .Eq ts1
          let (e, ts3) ← parseExpr fuel' ts2
          .ok (.LetDecl true tsig e, ts3)
      | _ => .error "Parse error in declaration"

  def parseDeclarations (fuel : Nat) (ts : List Token) : Except String (List CDeclaration × List Token) :=
    match fuel with
    | 0 => .error "Parser: out of fuel"
    | fuel' + 1 =>
      match ts with
      | []           => .ok ([], [])
      | .BrClose :: _ => .ok ([], ts)
      | _ => do
          let (d, ts1) ← parseDeclaration fuel' ts
          let (ds, ts2) ← parseDeclarations fuel' ts1
          .ok (d :: ds, ts2)
end

def parseTokens (ts : List Token) : Except String (List CDeclaration) := do
  let (decls, rest) ← parseDeclarations (ts.length * 4 + 20) ts
  if rest.isEmpty then .ok decls
  else .error "Parse error: unconsumed tokens"

/-- Full end-to-end Constructive Lean 4 pipeline on raw `.ma` source strings:
    `tokenize → parseTokens → scopeCheck → checkProgram`. -/
def checkSource (src : String) : Except String TCState := do
  let toks ← tokenize src
  let cdecls ← parseTokens toks
  let adecls ← scopeCheck cdecls
  checkProgram adecls

mutual
  def showVal : Val → String
    | .VSet        => "Set"
    | .VSize       => "Size"
    | .VInfty      => "#"
    | .VSucc v     => "($ " ++ showVal v ++ ")"
    | .VApp v vl   => "(" ++ showVal v ++ " " ++ showValList vl ++ ")"
    | .VCon _ n    => n
    | .VDef n      => n
    | .VGen k      => toString k
    | .VPi x av _ e => "(" ++ x ++ " : " ++ showVal av ++ ") -> " ++ prettyExpr e
    | .VLam x _ e   => "(\\" ++ x ++ " -> " ++ prettyExpr e ++ ")"

  def showValList : List Val → String
    | []      => ""
    | [v]     => showVal v
    | v :: vl => showVal v ++ " " ++ showValList vl
end

/-- Full end-to-end check and evaluation of `eval let` declarations (`Main.hs` lines 37–52). -/
def evalSource (src : String) : Except String (List String) := do
  let toks ← tokenize src
  let cdecls ← parseTokens toks
  let adecls ← scopeCheck cdecls
  let st ← checkProgram adecls
  let evalDecls := adecls.filterMap fun d =>
    match d with
    | .LetDecl true (.mk n _) e => some (n, e)
    | _                         => none
  evalDecls.mapM fun (n, e) =>
    match runTypeCheck st (whnf defaultFuel [] e) with
    | .ok (v, _) => .ok (n ++ " evaluates to " ++ showVal v)
    | .error err => .error err

end MugdaCore
