/-
  Mugda/Metatheory.lean
  =====================
  Stage II in-place metatheorems, universal erasure/substitution/SCT proofs,
  tightness theorems, and end-to-end verification suite proved directly on
  the Constructive Lean 4 compiler (`Mugda.Core`).
-/

import Mugda.Core
import Mugda.Soundness

namespace MugdaCore

/-! ## 0. Monad Unfolding Lemmas for `runTypeCheck` -/

@[simp] theorem runTypeCheck_pure (st : TCState) (a : α) :
    runTypeCheck st (pure a) = .ok (a, st) := rfl

@[simp] theorem runTypeCheck_bind (st : TCState) (m : TypeCheck α) (f : α → TypeCheck β) :
    runTypeCheck st (m >>= f) =
      match runTypeCheck st m with
      | .error err => .error err
      | .ok (a, st') => runTypeCheck st' (f a) := by
  unfold runTypeCheck StateT.run
  change Except.bind (m st) (fun x => f x.1 x.2) = _
  cases m st <;> rfl

/-! ## 1. Size Subtyping, Tower Laws & Erasure Metatheorems (Pillars II & III) -/

/-- **Theorem 1 (Runtime Size Idempotence at `#`)**:
    In `MugdaCore.sinfty` (`Value.hs` line 130), `$ # = #`. -/
theorem sinfty_infty : sinfty .VInfty = .VInfty := rfl

/-- **Theorem 2 (`completePatterns` Rejects `SuccP`)**:
    The ported `cp` checker rejects any `SuccP` pattern immediately (`Completness.hs` line 15). -/
theorem cp_succP_false (p : Pattern) : cp (.SuccP p) = false := rfl

/-- **Theorem 3 (`leqSize` Reflexivity & Top Element `#`)**:
    For every generic size variable `VGen k` and `#` (`VInfty`), `leqSize` succeeds. -/
theorem leqSize_infty (v : Val) (st : TCState) :
    runTypeCheck st (leqSize v .VInfty) = .ok ((), st) := rfl

theorem leqSize_gen_refl (k : Nat) (st : TCState) :
    runTypeCheck st (leqSize (.VGen k) (.VGen k)) = .ok ((), st) := by
  simp [leqSize, runTypeCheck]
  rfl

/-- **Theorem 4 (`leqSize` Unfolding Laws under `$` and Arbitrary `$^n` Towers)** -/
theorem leqSize_succ_gen (k : Nat) (v2 : Val) :
    leqSize (.VGen k) (.VSucc v2) = leqSize (.VGen k) v2 := rfl

theorem leqSize_succ_both (v1 v2 : Val) :
    leqSize (.VSucc v1) (.VSucc v2) = leqSize v1 v2 := rfl

/-- Iterated successor value `$^n v`. -/
def iterVSucc : Nat → Val → Val
  | 0,     v => v
  | n + 1, v => .VSucc (iterVSucc n v)

theorem leqSize_iterVSucc_gen (n k : Nat) (v : Val) :
    leqSize (.VGen k) (iterVSucc n v) = leqSize (.VGen k) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold iterVSucc
    rw [leqSize_succ_gen, ih]

theorem leqSize_iterVSucc_both (n : Nat) (v1 v2 : Val) :
    leqSize (iterVSucc n v1) (iterVSucc n v2) = leqSize v1 v2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold iterVSucc
    rw [leqSize_succ_both, ih]

theorem inst_succ_infty (fuel m : Nat) (flex : List Nat) (v : Val) :
    inst (fuel + 1) m flex (.VSucc v) .VInfty = inst fuel m flex v .VInfty := rfl

/-- **Theorem 5 (Universal `$^n` Tower Stripping in `inst` against `#`)**:
    Unifying `$^n v` with `#` (`.VInfty`) strips any finite number `n` of
    `.VSucc` constructors and reduces to unifying `v` with `.VInfty`. -/
theorem inst_iterVSucc_infty (n fuel m : Nat) (flex : List Nat) (v : Val) :
    inst (fuel + n) m flex (iterVSucc n v) .VInfty = inst fuel m flex v .VInfty := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h_add : fuel + (n + 1) = (fuel + n) + 1 := Nat.add_assoc fuel n 1
    rw [h_add, iterVSucc, inst_succ_infty, ih]

/-- **Theorem 6 (Size Erasure Invariance of `DotP` Matching)**:
    For any `.DotP e` pattern, `matchPat` never inspects whether the runtime value
    is a finite successor `.VSucc v` or erased `.VInfty` (`#`). -/
theorem matchPat_dotP_erased (fuel : Nat) (env : Env) (e : Expr) (v1 v2 : Val) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.DotP e) v1) =
    runTypeCheck st (matchPat (fuel + 1) env (.DotP e) v2) := rfl

/-- **Theorem 7 (Tightness of Bug 5 Fix — `SuccP` Breaks Runtime Size Erasure)**:
    If a clause were allowed to match on a successor size pattern `.SuccP (.VarP "i")`
    (which was permitted when `completeFun _ = True` in Mugda 2008), then matching against
    the un-erased size `.VSucc (.VGen 0)` binds `"i" ↦ .VGen 0`, whereas matching against
    its `#`-erasure `.VInfty` binds `"i" ↦ .VInfty`!
    This proves why `completePatterns` (`cp (.SuccP _) = false`) is necessary for size erasure. -/
theorem succP_breaks_size_erasure (st : TCState) :
    runTypeCheck st (matchPat 2 [] (.SuccP (.VarP "i")) (.VSucc (.VGen 0))) =
      .ok (some [("i", .VGen 0)], st) ∧
    runTypeCheck st (matchPat 2 [] (.SuccP (.VarP "i")) .VInfty) =
      .ok (some [("i", .VInfty)], st) ∧
    (some [("i", Val.VGen 0)] ≠ some [("i", Val.VInfty)]) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  injection h with hlist
  injection hlist with hhead _
  injection hhead with _ hv
  contradiction

/-! ## 2. Universal Size-Erasure Commutation for Complete Inductive Patterns (Pillar III) -/

/- Inductive patterns accepted by `cp` (no `.SuccP`, and all constructors `.ConP .Ind`). -/
mutual
  def isIndCompletePat : Pattern → Bool
    | .VarP _         => true
    | .DotP _         => true
    | .ConP .Ind _ pl => isIndCompletePatList pl
    | _               => false

  def isIndCompletePatList : List Pattern → Bool
    | []      => true
    | p :: pl => isIndCompletePat p && isIndCompletePatList pl
end

mutual
  theorem isIndCompletePat_imp_cp (p : Pattern) (h : isIndCompletePat p = true) :
      cp p = true := by
    cases p with
    | VarP _ => rfl
    | DotP _ => rfl
    | SuccP _ => contradiction
    | ConP co n pl =>
      cases co with
      | CoInd => contradiction
      | Ind =>
        unfold isIndCompletePat at h
        unfold cp
        exact isIndCompletePatList_imp_cpList pl h

  theorem isIndCompletePatList_imp_cpList (pl : List Pattern) (h : isIndCompletePatList pl = true) :
      cpList pl = true := by
    cases pl with
    | nil => rfl
    | cons p ps =>
      unfold isIndCompletePatList at h
      unfold cpList
      rw [Bool.and_eq_true] at h ⊢
      exact ⟨isIndCompletePat_imp_cp p h.1, isIndCompletePatList_imp_cpList ps h.2⟩
end

/- Runtime size erasure on `Val`: replaces every `.VSucc v` size with `.VInfty` (`#`)
   and recursively erases sizes inside constructor applications. -/
mutual
  def eraseSizesVal : Val → Val
    | .VSucc _              => .VInfty
    | .VApp (.VCon co y) vl => .VApp (.VCon co y) (eraseSizesValList vl)
    | v                     => v

  def eraseSizesValList : List Val → List Val
    | []      => []
    | v :: vl => eraseSizesVal v :: eraseSizesValList vl
end

def eraseSizesEnv : Env → Env
  | []            => []
  | (x, v) :: env => (x, eraseSizesVal v) :: eraseSizesEnv env

theorem eraseSizesEnv_updateEnv (env : Env) (x : Name) (v : Val) :
    eraseSizesEnv (updateEnv env x v) = updateEnv (eraseSizesEnv env) x (eraseSizesVal v) := by
  unfold updateEnv
  split <;> rfl

theorem matchPat_ind_nil_vcon (fuel : Nat) (env : Env) (x : Name) (co' : Co) (y : Name) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.ConP .Ind x []) (.VCon co' y)) =
      if x == y then .ok (some env, st) else .ok (none, st) := by
  change runTypeCheck st (if x == y then pure (some env) else pure none) = _
  cases (x == y) <;> rfl

theorem matchPat_ind_vapp_vcon (fuel : Nat) (env : Env) (x : Name) (pl : List Pattern) (co' : Co) (y : Name) (vl : List Val) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.ConP .Ind x pl) (.VApp (.VCon co' y) vl)) =
      if x == y then runTypeCheck st (matchList fuel env pl vl) else .ok (none, st) := by
  cases pl with
  | nil =>
    change runTypeCheck st (if x == y then matchList fuel env [] vl else pure none) = _
    cases (x == y) <;> rfl
  | cons q ql =>
    change runTypeCheck st (if x == y then matchList fuel env (q :: ql) vl else pure none) = _
    cases (x == y) <;> rfl

theorem matchList_cons (fuel : Nat) (env : Env) (p : Pattern) (pl : List Pattern) (v : Val) (vl : List Val) (st : TCState) :
    runTypeCheck st (matchList (fuel + 1) env (p :: pl) (v :: vl)) =
      match runTypeCheck st (matchPat fuel env p v) with
      | .error err => .error err
      | .ok (m, st1) =>
        match m with
        | some env' => runTypeCheck st1 (matchList fuel env' pl vl)
        | none => .ok (none, st1) := by
  conv => lhs; unfold matchList
  rw [runTypeCheck_bind]
  cases runTypeCheck st (matchPat fuel env p v) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨m, st1⟩
    cases m <;> rfl

/- **Theorem 8 (Universal Size-Erasure Commutation for `matchPat` and `matchList`)**:
   For every pattern `p` (and pattern spine `ps`) satisfying `isIndCompletePat`,
   matching `p` against the size-erased value `eraseSizesVal v0` in `eraseSizesEnv env`
   produces the exact size-erasure of matching `p` against `v0` in `env`. -/
mutual
  theorem matchPat_eraseSizes_comm
      (fuel : Nat) (env : Env) (p : Pattern) (v0 : Val) (st : TCState)
      (hp : isIndCompletePat p = true) :
      runTypeCheck st (matchPat fuel (eraseSizesEnv env) p (eraseSizesVal v0)) =
        (runTypeCheck st (matchPat fuel env p v0)).map
          (fun (res, st') => (res.map eraseSizesEnv, st')) := by
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      cases p with
      | DotP e => rfl
      | VarP x =>
        change Except.ok (some (updateEnv (eraseSizesEnv env) x (eraseSizesVal v0)), st) =
               Except.ok (some (eraseSizesEnv (updateEnv env x v0)), st)
        rw [eraseSizesEnv_updateEnv]
      | SuccP p' => contradiction
      | ConP co x pl =>
        cases co with
        | CoInd => contradiction
        | Ind =>
          unfold isIndCompletePat at hp
          cases pl with
          | nil =>
            cases v0 with
            | VCon co' y =>
              unfold eraseSizesVal
              rw [matchPat_ind_nil_vcon, matchPat_ind_nil_vcon]
              cases (x == y) <;> rfl
            | VApp u vl =>
              cases u with
              | VCon co' y =>
                unfold eraseSizesVal
                rw [matchPat_ind_vapp_vcon, matchPat_ind_vapp_vcon]
                cases (x == y) with
                | false => rfl
                | true => exact matchList_eraseSizes_comm fuel' env [] vl st rfl
              | _ => rfl
            | _ => rfl
          | cons q ql =>
            cases v0 with
            | VApp u vl =>
              cases u with
              | VCon co' y =>
                unfold eraseSizesVal
                rw [matchPat_ind_vapp_vcon, matchPat_ind_vapp_vcon]
                cases (x == y) with
                | false => rfl
                | true => exact matchList_eraseSizes_comm fuel' env (q :: ql) vl st hp
              | _ => rfl
            | _ => rfl

  theorem matchList_eraseSizes_comm
      (fuel : Nat) (env : Env) (ps : List Pattern) (vs : List Val) (st : TCState)
      (hps : isIndCompletePatList ps = true) :
      runTypeCheck st (matchList fuel (eraseSizesEnv env) ps (eraseSizesValList vs)) =
        (runTypeCheck st (matchList fuel env ps vs)).map
          (fun (res, st') => (res.map eraseSizesEnv, st')) := by
    cases fuel with
    | zero => rfl
    | succ fuel' =>
      cases ps with
      | nil =>
        cases vs <;> rfl
      | cons p pl =>
        cases vs with
        | nil => rfl
        | cons v vl =>
          unfold isIndCompletePatList at hps
          rw [Bool.and_eq_true] at hps
          have ih1 := matchPat_eraseSizes_comm fuel' env p v st hps.1
          unfold eraseSizesValList
          rw [matchList_cons, matchList_cons, ih1]
          cases h1 : runTypeCheck st (matchPat fuel' env p v) with
          | error err => rfl
          | ok resSt =>
            rcases resSt with ⟨m, st1⟩
            cases m with
            | none => rfl
            | some env' =>
              exact matchList_eraseSizes_comm fuel' env' pl vl st1 hps.2
end

/-! ## 3. Universal `nocc`, `substVal`, `checkNoccEnv` & `checkNoccDomains` Theorems (Pillar I & II) -/

/-- **Theorem 9 (`nocc` on Generic Variables)**:
    `nocc (fuel + 1) k (.VGen j) (.VGen i)` evaluates directly to `j != i`. -/
theorem nocc_vgen_eq (fuel k j i : Nat) (st : TCState) :
    runTypeCheck st (nocc (fuel + 1) k (.VGen j) (.VGen i)) = .ok (j != i, st) := rfl

theorem lookupSubst_single_of_ne (j i : Nat) (sv : Val) (h : (j != i) = true) :
    lookupSubst i [(j, sv)] = none := by
  unfold lookupSubst
  have hij : (i == j) = false := by
    rw [bne_iff_ne] at h
    exact beq_eq_false_iff_ne.mpr (Ne.symm h)
  rw [hij]
  rfl

def isNotVInfty : Val → Bool
  | .VInfty => false
  | _       => true

/-- Pure size or atomic values containing no unreduced `.VSucc .VInfty` redex. -/
def isNormSizeOrAtom : Val → Bool
  | .VSet     => true
  | .VSize    => true
  | .VInfty   => true
  | .VCon _ _ => true
  | .VDef _   => true
  | .VGen _   => true
  | .VSucc v  => isNotVInfty v && isNormSizeOrAtom v
  | _         => false

theorem substVal_vgen (fuel : Nat) (sub : Substitution) (i : Nat) (st : TCState) :
    runTypeCheck st (substVal (fuel + 1) sub (.VGen i)) =
      match lookupSubst i sub with
      | none    => .ok (.VGen i, st)
      | some v' => .ok (v', st) := by
  change runTypeCheck st
           (match lookupSubst i sub with
            | none    => pure (.VGen i)
            | some v' => pure v') = _
  cases lookupSubst i sub <;> rfl

theorem substVal_vsucc (fuel : Nat) (sub : Substitution) (v : Val) (st : TCState) :
    runTypeCheck st (substVal (fuel + 1) sub (.VSucc v)) =
      match runTypeCheck st (substVal fuel sub v) with
      | .error err => .error err
      | .ok (v1', st1) => .ok (sinfty v1', st1) := by
  conv => lhs; unfold substVal
  rw [runTypeCheck_bind]
  cases runTypeCheck st (substVal fuel sub v) <;> rfl

/-- **Theorem 10 (Universal `nocc` → `substVal` Identity Law on Size & Atomic Values)**:
    For every normalized size/atomic value `tv`, if `nocc fuel k (.VGen j) tv` succeeds with
    `true`, then substituting `j ↦ sv` via `substVal fuel [(j, sv)] tv` leaves `tv` unchanged. -/
theorem nocc_substVal_id_of_normSizeOrAtom
    (fuel k j : Nat) (sv tv : Val) (st st' : TCState)
    (hnorm : isNormSizeOrAtom tv = true)
    (hnocc : runTypeCheck st (nocc fuel k (.VGen j) tv) = .ok (true, st')) :
    runTypeCheck st (substVal fuel [(j, sv)] tv) = .ok (tv, st) ∧ st' = st := by
  induction fuel generalizing tv st st' with
  | zero => contradiction
  | succ fuel' ih =>
    cases tv with
    | VSet =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VSize =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VInfty =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VCon co n =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VDef n =>
      injection hnocc with hpair
      injection hpair with _ hst
      exact ⟨rfl, hst.symm⟩
    | VGen i =>
      rw [nocc_vgen_eq] at hnocc
      injection hnocc with hpair
      injection hpair with hb hst
      rw [substVal_vgen, lookupSubst_single_of_ne j i sv hb]
      exact ⟨rfl, hst.symm⟩
    | VSucc v =>
      unfold isNormSizeOrAtom at hnorm
      rw [Bool.and_eq_true] at hnorm
      unfold nocc at hnocc
      have ⟨hsub, hst⟩ := ih v st st' hnorm.2 hnocc
      refine ⟨?_, hst⟩
      rw [substVal_vsucc, hsub]
      cases v <;> first | rfl | contradiction
    | VApp _ _ => contradiction
    | VPi _ _ _ _ => contradiction
    | VLam _ _ _ => contradiction

theorem checkNoccEnv_cons (fuel k j : Nat) (x : Name) (tv : TVal) (gamma : Env) (st : TCState) :
    runTypeCheck st (checkNoccEnv fuel k j ((x, tv) :: gamma)) =
      match runTypeCheck st (nocc fuel k (.VGen j) tv) with
      | .error err => .error err
      | .ok (b, st1) =>
        if b then runTypeCheck st1 (checkNoccEnv fuel k j gamma)
        else .error "unsound size refinement in pattern: size variable occurs in another pattern variable's type" := by
  conv => lhs; unfold checkNoccEnv
  rw [runTypeCheck_bind]
  cases runTypeCheck st (nocc fuel k (.VGen j) tv) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨b, st1⟩
    cases b <;> rfl

/-- **Theorem 11 (Universal Soundness of `checkNoccEnv`)**:
    If `checkNoccEnv fuel k j gamma` succeeds, then every variable binding `(x, tv)`
    in `gamma` satisfies `nocc fuel k (.VGen j) tv = true`. -/
theorem checkNoccEnv_head
    (fuel k j : Nat) (x : Name) (tv : TVal) (gamma : Env) (st st' : TCState)
    (h : runTypeCheck st (checkNoccEnv fuel k j ((x, tv) :: gamma)) = .ok ((), st')) :
    ∃ st1, runTypeCheck st (nocc fuel k (.VGen j) tv) = .ok (true, st1) ∧
           runTypeCheck st1 (checkNoccEnv fuel k j gamma) = .ok ((), st') := by
  rw [checkNoccEnv_cons] at h
  cases hn : runTypeCheck st (nocc fuel k (.VGen j) tv) with
  | error err =>
    rw [hn] at h
    contradiction
  | ok res =>
    rcases res with ⟨b, st1⟩
    rw [hn] at h
    cases b with
    | false => contradiction
    | true => exact ⟨st1, rfl, h⟩

theorem checkNoccEnv_forall_mem
    (fuel k j : Nat) (gamma : Env) (st st' : TCState)
    (h : runTypeCheck st (checkNoccEnv fuel k j gamma) = .ok ((), st'))
    (p : Name × Val) (hp : p ∈ gamma) :
    ∃ st1 st2, runTypeCheck st1 (nocc fuel k (.VGen j) p.2) = .ok (true, st2) := by
  induction gamma generalizing st with
  | nil => contradiction
  | cons hd tl ih =>
    rcases hd with ⟨x, tv⟩
    have ⟨st1, hn, htl⟩ := checkNoccEnv_head fuel k j x tv tl st st' h
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨st, st1, hn⟩
    · exact ih st1 htl hmem

theorem checkNoccDomains_vpi (fuel k j : Nat) (x : Name) (av : TVal) (env : Env) (b : Expr) (st : TCState) :
    runTypeCheck st (checkNoccDomains (fuel + 1) k j (.VPi x av env b)) =
      match runTypeCheck st (nocc fuel k (.VGen j) av) with
      | .error err => .error err
      | .ok (ok, st1) =>
        if !ok then .error "unsound size refinement in pattern: size variable shared across multiple arguments or branches"
        else
          match runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) with
          | .error err => .error err
          | .ok (bv, st2) => runTypeCheck st2 (checkNoccDomains fuel (k + 1) j bv) := by
  conv => lhs; unfold checkNoccDomains
  rw [runTypeCheck_bind]
  cases runTypeCheck st (nocc fuel k (.VGen j) av) with
  | error err => rfl
  | ok res =>
    rcases res with ⟨ok, st1⟩
    cases ok with
    | false => rfl
    | true =>
      dsimp
      change runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b >>= fun bv => checkNoccDomains fuel (k + 1) j bv) = _
      rw [runTypeCheck_bind]
      cases runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) <;> rfl

/-- **Theorem 12 (Universal Soundness of `checkNoccDomains` on Pi Telescopes)**:
    If `checkNoccDomains (fuel + 1) k j (.VPi x av env b)` succeeds, then `nocc` succeeds
    with `true` on the domain `av` and `checkNoccDomains` succeeds on the codomain `bv`. -/
theorem checkNoccDomains_pi
    (fuel k j : Nat) (x : Name) (av : TVal) (env : Env) (b : Expr) (st st' : TCState)
    (h : runTypeCheck st (checkNoccDomains (fuel + 1) k j (.VPi x av env b)) = .ok ((), st')) :
    ∃ st1 bv st2,
      runTypeCheck st (nocc fuel k (.VGen j) av) = .ok (true, st1) ∧
      runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) = .ok (bv, st2) ∧
      runTypeCheck st2 (checkNoccDomains fuel (k + 1) j bv) = .ok ((), st') := by
  rw [checkNoccDomains_vpi] at h
  cases hn : runTypeCheck st (nocc fuel k (.VGen j) av) with
  | error err =>
    rw [hn] at h
    contradiction
  | ok res =>
    rcases res with ⟨ok, st1⟩
    rw [hn] at h
    cases ok with
    | false => contradiction
    | true =>
      change (match runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) with
              | Except.error err => Except.error err
              | Except.ok (bv, st2) => runTypeCheck st2 (checkNoccDomains fuel (k + 1) j bv)) = Except.ok ((), st') at h
      cases hw : runTypeCheck st1 (whnf fuel (updateEnv env x (.VGen k)) b) with
      | error err =>
        rw [hw] at h
        contradiction
      | ok res2 =>
        rcases res2 with ⟨bv, st2⟩
        rw [hw] at h
        exact ⟨st1, bv, st2, rfl, hw, h⟩

/-! ## 4. Matrix Order `ORDER_+` Semiring, Diagonal Witness & Ordinal Soundness (Pillars I & V) -/

/-- Scalar orders `{.Lt, .Le, .Un}` (excluding `.Mat`). -/
def isScalarOrder : Order → Bool
  | .Mat _ => false
  | _      => true

/-- **Theorem 13 (Commutativity, Associativity & Distributivity of Scalar `Order` Semiring)** -/
theorem minScalar_comm (a b : Order) : minScalar a b = minScalar b a := by
  cases a <;> cases b <;> rfl

theorem minScalar_assoc (a b c : Order) :
    minScalar (minScalar a b) c = minScalar a (minScalar b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem maxScalar_comm (a b : Order) : maxScalar a b = maxScalar b a := by
  cases a <;> cases b <;> rfl

theorem maxScalar_assoc (a b c : Order)
    (ha : isScalarOrder a = true) (hb : isScalarOrder b = true) (hc : isScalarOrder c = true) :
    maxScalar (maxScalar a b) c = maxScalar a (maxScalar b c) := by
  cases a <;> cases b <;> cases c <;> first | rfl | contradiction

theorem compScalar_assoc (a b c : Order) :
    compScalar (compScalar a b) c = compScalar a (compScalar b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem compScalar_maxScalar_distrib_left (a b c : Order)
    (hb : isScalarOrder b = true) (hc : isScalarOrder c = true) :
    compScalar a (maxScalar b c) = maxScalar (compScalar a b) (compScalar a c) := by
  cases a <;> cases b <;> cases c <;> first | rfl | contradiction

theorem compScalar_maxScalar_distrib_right (a b c : Order)
    (ha : isScalarOrder a = true) (hb : isScalarOrder b = true) :
    compScalar (maxScalar a b) c = maxScalar (compScalar a c) (compScalar b c) := by
  cases a <;> cases b <;> cases c <;> first | rfl | contradiction

/-- **Theorem 14 (Bug 3b Fix — `maxO` on Two Matrices and `collapseOrder` Always Collapse to Scalars)**:
    Combining two `.Mat` values via `maxO` (or collapsing any `Order` via `collapseOrder`)
    can never produce a nested `.Mat m`. -/
theorem maxO_mat_never_mat (m1 m2 m : Matrix Order) :
    maxO (.Mat m1) (.Mat m2) ≠ .Mat m := by
  change maxScalar (collapseOrder (.Mat m1)) (collapseOrder (.Mat m2)) ≠ .Mat m
  unfold maxScalar
  split <;> intro h <;> injection h

theorem collapseOrder_never_mat (o : Order) (m : Matrix Order) :
    collapseOrder o ≠ .Mat m := by
  cases o with
  | Lt => intro h; injection h
  | Le => intro h; injection h
  | Un => intro h; injection h
  | Mat rows =>
    unfold collapseOrder
    cases rows with
    | nil => intro h; injection h
    | cons r rs =>
      cases rs with
      | nil =>
        unfold collapseRows
        cases r with
        | nil => intro h; injection h
        | cons o0 os =>
          unfold collapseElemAt
          exact collapseOrder_never_mat o0 m
      | cons r2 rs2 =>
        unfold collapseRows minScalar
        split <;> intro h <;> injection h

/-- **Theorem 15 (Universal Diagonal Witness Characterization of `isDecr` and `checkIdem`)**:
    A matrix `.Mat m` satisfies `isDecr (.Mat m) = true` if and only if there exists a
    diagonal index `k` and entry `o` at `(k, k)` of `m` such that `isDecr o = true`. -/
theorem isDecrElemAt_iff (i : Nat) (r : List Order) :
    isDecrElemAt i r = true ↔ ∃ o, getElemOpt r i = some o ∧ isDecr o = true := by
  induction r generalizing i with
  | nil =>
    unfold isDecrElemAt getElemOpt
    simp
  | cons o os ih =>
    cases i with
    | zero =>
      unfold isDecrElemAt getElemOpt
      simp
    | succ i' =>
      unfold isDecrElemAt getElemOpt
      exact ih i'

theorem isDecrRows_iff (i : Nat) (rows : List (List Order)) :
    isDecrRows i rows = true ↔
      ∃ k row o, getElemOpt rows k = some row ∧ getElemOpt row (i + k) = some o ∧ isDecr o = true := by
  induction rows generalizing i with
  | nil =>
    unfold isDecrRows getElemOpt
    simp
  | cons r rs ih =>
    unfold isDecrRows
    rw [Bool.or_eq_true, isDecrElemAt_iff, ih (i + 1)]
    constructor
    · rintro (⟨o, ho, hdecr⟩ | ⟨k, row, o, hrow, ho, hdecr⟩)
      · refine ⟨0, r, o, rfl, ?_, hdecr⟩
        simpa using ho
      · refine ⟨k + 1, row, o, hrow, ?_, hdecr⟩
        have h_add : i + (k + 1) = (i + 1) + k := by omega
        rw [h_add]
        exact ho
    · rintro ⟨k, row, o, hrow, ho, hdecr⟩
      cases k with
      | zero =>
        unfold getElemOpt at hrow
        injection hrow with hr
        subst hr
        left
        refine ⟨o, ?_, hdecr⟩
        simpa using ho
      | succ k' =>
        unfold getElemOpt at hrow
        right
        refine ⟨k', row, o, hrow, ?_, hdecr⟩
        have h_add : (i + 1) + k' = i + (k' + 1) := by omega
        rw [h_add]
        exact ho

theorem isDecr_mat_iff (m : Matrix Order) :
    isDecr (.Mat m) = true ↔
      ∃ k row o, getElemOpt m k = some row ∧ getElemOpt row k = some o ∧ isDecr o = true := by
  change isDecrRows 0 m = true ↔ _
  have h := isDecrRows_iff 0 m
  simpa [Nat.zero_add] using h

theorem checkIdem_sound (c : Call)
    (h_idem : (c == callComb c c) = true)
    (h_ok : checkIdem c = true) :
    ∃ k row o,
      getElemOpt (callComb c c).matrix k = some row ∧
      getElemOpt row k = some o ∧
      isDecr o = true := by
  change (!(c == callComb c c) || isDecr (.Mat (callComb c c).matrix)) = true at h_ok
  rw [h_idem] at h_ok
  exact (isDecr_mat_iff (callComb c c).matrix).mp h_ok

theorem checkAll_sound
    (calls : List Call) (c : Call)
    (hall : checkAll calls = true)
    (hc : c ∈ calls)
    (hidem : (c == callComb c c) = true) :
    ∃ k row o,
      getElemOpt (callComb c c).matrix k = some row ∧
      getElemOpt row k = some o ∧
      isDecr o = true := by
  unfold checkAll at hall
  rw [List.all_eq_true] at hall
  exact checkIdem_sound c hidem (hall c hc)

/-- **Theorem 16 (Semantic Soundness & Well-Foundedness of `Order` on Transfinite Ordinals `SizeOrd`)**:
    Interpreting `.Lt` as strict transfinite ordinal decrease `<`, `.Le` as `≤`, and `.Un`
    as `True` on `MugdaSoundness.SizeOrd`, `compScalar` is sound with respect to relational
    composition, `minScalar` is sound with respect to conjunction, and no infinite sequence
    of `.Lt` steps can exist. -/
def evalScalarOrd : Order → MugdaSoundness.SizeOrd → MugdaSoundness.SizeOrd → Prop
  | .Lt => (· < ·)
  | .Le => (· ≤ ·)
  | _   => fun _ _ => True

theorem compScalar_sound_sizeOrd
    (o1 o2 : Order) (α β γ : MugdaSoundness.SizeOrd)
    (h1 : evalScalarOrd o1 α β)
    (h2 : evalScalarOrd o2 β γ) :
    evalScalarOrd (compScalar o1 o2) α γ := by
  cases o1 <;> cases o2 <;> try trivial
  · -- Lt, Lt
    exact MugdaSoundness.SizeOrd.lt_trans h1 h2
  · -- Lt, Le
    exact MugdaSoundness.SizeOrd.lt_of_succ_le_of_le h1 h2
  · -- Le, Lt
    rcases h1 with hlt | rfl
    · exact MugdaSoundness.SizeOrd.lt_trans hlt h2
    · exact h2
  · -- Le, Le
    exact MugdaSoundness.SizeOrd.le_trans h1 h2

theorem minScalar_sound_sizeOrd
    (o1 o2 : Order) (α β : MugdaSoundness.SizeOrd)
    (h1 : evalScalarOrd o1 α β)
    (h2 : evalScalarOrd o2 α β) :
    evalScalarOrd (minScalar o1 o2) α β := by
  cases o1 <;> cases o2 <;> first | trivial | exact h1 | exact Or.inl h1

theorem no_infinite_decr_sizeOrd (f : Nat → MugdaSoundness.SizeOrd) :
    ¬ (∀ n, evalScalarOrd .Lt (f (n + 1)) (f n)) := by
  intro h
  have hacc : ∀ α, Acc MugdaSoundness.SizeOrd.lt α → ∀ m, f m = α → False := by
    intro α hacc
    induction hacc with
    | intro x _ ih =>
      intro m hm
      subst hm
      exact ih (f (m + 1)) (h m) (m + 1) rfl
  exact hacc (f 0) (MugdaSoundness.SizeOrd.wf_lt.apply (f 0)) 0 rfl

/-- **Theorem 17 (Bug 3a Fix — `isPurePat` Excludes `DotP` and `SuccP`)**:
    `isPurePat` returns `false` on `.DotP` and `.SuccP`, ensuring `compareExpr` never
    constructs a `Mat` matrix for sized constructors with dot-pattern size indices. -/
theorem isPurePat_dotP_false (e : Expr) : isPurePat (.DotP e) = false := rfl
theorem isPurePat_succP_false (p : Pattern) : isPurePat (.SuccP p) = false := rfl

/-- **Theorem 18 (Bug 4 Fix — `collectCallsExpr` Extracts Calls from `LLet` Bound Expressions)**:
    Every call extracted from `e1` is included in the calls extracted from `.LLet x t1 e1 e2`. -/
theorem collectCalls_llet_includes_bound
    (nl : List (Name × Nat)) (f : Name) (pl : List Pattern)
    (x : Name) (t1 e1 e2 : Expr) (c : Call)
    (hc : c ∈ collectCallsExpr nl f pl e1) :
    c ∈ collectCallsExpr nl f pl (.LLet x t1 e1 e2) := by
  unfold collectCallsExpr
  exact List.mem_append_left _ (List.mem_append_right _ hc)

/-! ## 5. End-to-End Positive Expressiveness & Counterexample Suite (`native_decide`) -/

section VerificationSuite

/-- `sized data SNat : Size -> Set { zero : (i : Size) -> SNat ($ i) ; succ : (i : Size) -> SNat i -> SNat ($ i) }` -/
def snatDecl : Declaration :=
  .DataDecl "SNat" .Sized .Ind [] [] (.Pi "i" .Size .Set)
    [ .mk "zero" (.Pi "i" .Size (.App (.Def "SNat") [.Succ (.Var "i")]))
    , .mk "succ" (.Pi "i" .Size (.Pi "" (.App (.Def "SNat") [.Var "i"]) (.App (.Def "SNat") [.Succ (.Var "i")])))
    ]

/-- `fun sub : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i` (Euclidean subtraction, `examples/snat.ma`) -/
def subDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "sub"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.Pi "j" .Size
               (.Pi "" (.App (.Def "SNat") [.Var "j"])
                 (.App (.Def "SNat") [.Var "i"])))))
     , [ .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "zero" [.VarP "i"], .VarP "j", .VarP "y"]
             (.App (.Con .Ind "zero") [.Var "i"])
       , .mk [.VarP "i", .VarP "x", .DotP (.Succ (.Var "j")), .ConP .Ind "zero" [.VarP "j"]]
             (.Var "x")
       , .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "succ" [.VarP "i", .VarP "x"],
              .DotP (.Succ (.Var "j")), .ConP .Ind "succ" [.VarP "j", .VarP "y"]]
             (.App (.Def "sub") [.Succ (.Var "i"), .Var "x", .Var "j", .Var "y"])
       ]
     )]

/-- Counterexample `snat_mat_bug.ma` (Bugs 1 & 3):
    `fun loop : (i : Size) -> SNat i -> SNat i -> SNat #` -/
def snatMatBugDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "loop"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.Pi "" (.App (.Def "SNat") [.Var "i"])
               (.App (.Def "SNat") [.Infty]))))
     , [ .mk [ .DotP (.Succ (.Succ (.Succ (.Var "i"))))
             , .ConP .Ind "succ" [.DotP (.Succ (.Succ (.Var "i"))),
                 .ConP .Ind "succ" [.DotP (.Succ (.Var "i")),
                   .ConP .Ind "succ" [.VarP "i", .VarP "z"]]]
             , .ConP .Ind "succ" [.DotP (.Succ (.Succ (.Var "i"))),
                 .ConP .Ind "succ" [.DotP (.Succ (.Var "i")), .VarP "w"]]
             ]
             (.App (.Def "loop")
               [ .Succ (.Succ (.Succ (.Var "i")))
               , .App (.Con .Ind "succ") [.Succ (.Var "i"), .Var "w"]
               , .App (.Con .Ind "succ") [.Succ (.Succ (.Var "i")),
                   .App (.Con .Ind "succ") [.Succ (.Var "i"), .Var "w"]]
               ])
       ]
     )]

/-- **Verified Test 1 (Positive Adequacy — `SNat` + `sub`)** -/
theorem snat_and_sub_accepted :
    (checkProgram [snatDecl, subDecl]).isOk = true := by native_decide

/-- **Verified Test 2 (Counterexample Rejection — Bug 1 & Bug 3 `snat_mat_bug.ma`)** -/
theorem snat_mat_bug_rejected :
    (checkProgram [snatDecl, snatMatBugDecl]).isOk = false := by native_decide

/-- `sized data Wrap (+ A : Set) : Size -> Set { wrap : (i : Size) -> A -> Wrap A ($ i) }` -/
def wrapDecl : Declaration :=
  .DataDecl "Wrap" .Sized .Ind [.SPos] [("A", .Set)] (.Pi "i" .Size .Set)
    [ .mk "wrap" (.Pi "i" .Size (.Pi "" (.Var "A") (.App (.Def "Wrap") [.Var "A", .Succ (.Var "i")]))) ]

/-- Counterexample `loop_wrapped.ma` (Bugs 1 & 2) -/
def badWrapFunDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "badWrap"
         (.Pi "j" .Size
           (.Pi "" (.App (.Def "Wrap") [.Pi "" (.App (.Def "SNat") [.Var "j"]) (.App (.Def "SNat") [.Infty]), .Var "j"])
             (.Pi "" (.App (.Def "SNat") [.Var "j"])
               (.App (.Def "SNat") [.Infty]))))
     , [ .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "wrap" [.VarP "i", .VarP "f"], .VarP "x"]
             (.App (.Var "f") [.Var "x"])
       ]
     )]

/-- **Verified Test 3 (Counterexample Rejection — Bug 1 & Bug 2 `Wrap` Parameter Smuggling)** -/
theorem loop_wrapped_rejected :
    (checkProgram [snatDecl, wrapDecl, badWrapFunDecl]).isOk = false := by native_decide

/-- Counterexample `llet_bug.ma` (Bug 4 — recursive call hidden inside a local `let` binding) -/
def lletBugDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "loopLet"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.App (.Def "SNat") [.Infty])))
     , [ .mk [.VarP "i", .VarP "x"]
             (.LLet "y" (.App (.Def "SNat") [.Infty])
               (.App (.Def "loopLet") [.Var "i", .Var "x"])
               (.Var "y"))
       ]
     )]

/-- **Verified Test 4 (Counterexample Rejection — Bug 4 `LLet` Call Extraction)** -/
theorem llet_bug_rejected :
    (checkProgram [snatDecl, lletBugDecl]).isOk = false := by native_decide

/-- **Verified Test 5 (End-to-End `.ma` Source — Euclidean Division `div` in `examples/snat.ma`)** -/
def snatDivSource : String := "
sized data SNat : Size -> Set
{ zero : (i : Size) -> SNat ($ i)
; succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun sub : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ sub .($ i) (zero i) j y = zero i
; sub i x .($ j) (zero j) = x
; sub .($ i) (succ i x) .($ j) (succ j y) = sub ($ i) x j y
}

fun div : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ div .($ i) (zero i) j y = zero i
; div .($ i) (succ i x) j y = succ i (div i (sub i x j y) j y)
}
"

theorem snat_div_source_accepted :
    (checkSource snatDivSource).isOk = true := by native_decide

/-- **Verified Test 6 (End-to-End `.ma` Source Rejection — Cody Roux's `cody_nowraps.ma`)** -/
def codyNoWrapsSource : String := "
data Nat : Set
{ zero : Nat
; succ : Nat -> Nat
}

sized data O : Size -> Set
{ Z : (i : Size) -> O ($ i)
; S : (i : Size) -> O i -> O ($ i)
; L : (i : Size) -> (Nat -> O i) -> O ($ i)
; M : (i : Size) -> O i -> O i -> O ($ i)
}

fun loop : (i : Size) -> O i -> O i -> Nat
{ loop .($ ($ ($ i)))
       (M .($ ($ i)) (L .($ i) g) (Z .($ i)))
       (M .($ ($ i)) (L .($ i) f) (S .($ i) (S i z)))
  = loop ($ ($ i))
         (M ($ i) (L i g) (Z i))
         (M ($ i) (g zero) (f zero))
; loop i x y = zero
}
"

theorem cody_nowraps_source_rejected :
    (checkSource codyNoWrapsSource).isOk = false := by native_decide

/-- **Verified Test 7 (End-to-End Coinductive Fibonacci Stream & Evaluation — `examples/fib.ma`)** -/
def fibSource : String := "
data Nat : Set {
  zero : Nat;
  succ : Nat -> Nat
}

fun add : Nat -> Nat -> Nat {
  add zero = \\y -> y;
  add (succ x) = \\y -> succ (add x y)
}

sized codata Stream : Size -> Set {
  cons : (i : Size) -> Nat -> Stream i -> Stream ($ i)
}

fun tail : Stream # -> Stream # {
  tail (cons .# x xs) = xs
}

fun head : Stream # -> Nat {
  head (cons .# x xs) = x
}

fun nth : Nat -> Stream # -> Nat {
  nth zero xs = head xs;
  nth (succ x) xs = nth x (tail xs)
}

let 1 : Nat = (succ zero)

cofun fib' : (x : Nat) -> (y : Nat) -> (i : Size) -> Stream i {
  fib' x y ($ i) = cons i x (fib' y (add x y) i)
}

let fib : Stream # = (fib' 1 1 #)
let 4 : Nat = (succ (succ (succ 1)))
eval let fib4 : Nat = nth 4 fib
"

theorem fib_source_evaluates_to_5 :
    (evalSource fibSource).toOption =
    some ["fib4 evaluates to (succ (succ (succ (succ (succ zero)))))"] := by native_decide

/-- **Verified Test 8 (End-to-End `ORDER_+` Matrix Termination — `addpair` and `ack` in `examples/natpair.ma`)** -/
def natpairSource : String := "
data Nat : Set {
  zero : Nat;
  succ : Nat -> Nat
}

data NatPair : Set {
  Pair : Nat -> Nat -> NatPair
}

fun addpair : NatPair -> Nat {
  addpair (Pair x zero) = x;
  addpair (Pair x (succ y)) = succ (addpair (Pair x y))
}

fun ack : NatPair -> Nat {
  ack (Pair zero y) = succ y;
  ack (Pair (succ x) zero) = ack (Pair x (succ zero));
  ack (Pair (succ x) (succ y)) = ack (Pair x (ack (Pair (succ x) y)))
}
"

theorem natpair_source_accepted :
    (checkSource natpairSource).isOk = true := by native_decide

end VerificationSuite

end MugdaCore
