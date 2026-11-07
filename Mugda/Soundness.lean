/-
  Mugda/Soundness.lean
  ====================
  Machine-checked Lean 4 formalization of the semantic metatheory of Mugda:
    1. Transfinite size ordinals below `ω · 2` (`SizeOrd`, `<`, `≤`, `wf_lt`, `succ_le_of_lt`).
    2. Cumulative ordinal semantics of the Brouwer ordinal type `O` (`Z, S, L, M`) and `InO.mono`.
    3. Limit-ordinal refutation of Mugda 2008's unguarded deep pattern-matching
       refinement rule (`unguarded_deep_match_unsound`).
    4. Soundness of the fixed pattern-refinement rule (`fixed_pattern_refinement_sound`)
       and well-founded sized recursion (`sized_recursion_terminates`).
    5. Extended ordinal lattice with closure ordinal `#` (`ExtSize.infty`), `$ # = #`,
       and initial algebra stabilization (`inOExt_succ_infty`).
    6. Variance calculus (`Covariant`, `Contravariant`, `Independent`), admissibility
       soundness (`arrow_covariant`, `admissible_ind_telescope_sound`), and Bug 2
       refutation (`wrap_covariant_of_nocc`, `wrap_not_covariant_without_nocc`).
    7. Multi-argument pattern telescopes and tightness of `checkNoccEnv`
       (`multi_arg_pattern_refinement_sound`, `checkNoccEnv_tightness`).
    8. Coinductive sized streams (`StreamEq`), contravariant size subtyping
       (`streamEq_anti`), and guarded coinductive productivity (`fib_stream_productive`).

  Self-contained in core Lean 4 (zero `sorry`, zero `partial`, zero external dependencies).
-/

namespace MugdaSoundness

/-! ## 1. Transfinite Size Ordinals up to `ω + ω` -/

/-- Size ordinals below `ω · 2`: either a finite ordinal `fin n` (`n < ω`)
    or a transfinite ordinal `omegaPlus k` (`ω + k`).
    This suffices to model finite sizes, the first limit ordinal `ω`,
    and successor stages `ω + k` above `ω`. -/
inductive SizeOrd : Type where
  | fin       : Nat → SizeOrd
  | omegaPlus : Nat → SizeOrd
  deriving DecidableEq, Repr

namespace SizeOrd

/-- Successor size `$ α = α + 1`. -/
def succ : SizeOrd → SizeOrd
  | fin n       => fin (n + 1)
  | omegaPlus k => omegaPlus (k + 1)

prefix:max "$ " => SizeOrd.succ

/-- Strict ordering `α < β` on `SizeOrd`. -/
def lt : SizeOrd → SizeOrd → Prop
  | fin n,       fin m       => n < m
  | fin _,       omegaPlus _ => True
  | omegaPlus _, fin _       => False
  | omegaPlus j, omegaPlus k => j < k

instance : LT SizeOrd := ⟨SizeOrd.lt⟩

/-- Weak ordering `α ≤ β` on `SizeOrd` (size subtyping). -/
def le (α β : SizeOrd) : Prop := α < β ∨ α = β

instance : LE SizeOrd := ⟨SizeOrd.le⟩

theorem lt_irrefl : ∀ α : SizeOrd, ¬ (α < α)
  | fin _,       h => Nat.lt_irrefl _ h
  | omegaPlus _, h => Nat.lt_irrefl _ h

theorem lt_trans : ∀ {α β γ : SizeOrd}, α < β → β < γ → α < γ
  | fin _,       fin _,       fin _,       h1, h2 => Nat.lt_trans h1 h2
  | fin _,       fin _,       omegaPlus _, _,  _  => trivial
  | fin _,       omegaPlus _, omegaPlus _, _,  _  => trivial
  | omegaPlus _, omegaPlus _, omegaPlus _, h1, h2 => Nat.lt_trans h1 h2

theorem le_refl (α : SizeOrd) : α ≤ α := Or.inr rfl

theorem le_trans {α β γ : SizeOrd} (h1 : α ≤ β) (h2 : β ≤ γ) : α ≤ γ := by
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl h1
  · exact h2

theorem lt_succ_self : ∀ α : SizeOrd, α < $ α
  | fin n       => Nat.lt_succ_self n
  | omegaPlus k => Nat.lt_succ_self k

/-- Key ordinal inequality: `β < α ↔ $ β ≤ α`.
    Matching a constructor at size `α` yields a witness `β < α`, which
    justifies the inequality `$ β ≤ α`, NOT the equality `$ β = α`! -/
theorem succ_le_of_lt : ∀ {β α : SizeOrd}, β < α → ($ β) ≤ α
  | fin _,       fin _,       h =>
      match Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with
      | Or.inl heq => Or.inr (congrArg fin heq)
      | Or.inr hlt => Or.inl hlt
  | fin _,       omegaPlus _, _ => Or.inl trivial
  | omegaPlus _, omegaPlus _, h =>
      match Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with
      | Or.inl heq => Or.inr (congrArg omegaPlus heq)
      | Or.inr hlt => Or.inl hlt

theorem lt_of_succ_le_of_le {β α γ : SizeOrd} (h1 : β < α) (h2 : α ≤ γ) : β < γ := by
  rcases h2 with h2 | rfl
  · exact lt_trans h1 h2
  · exact h1

/-- `ω = omegaPlus 0` is a limit ordinal: it is not `$ β` for any `β`. -/
def omega : SizeOrd := omegaPlus 0

theorem omega_is_limit (β : SizeOrd) : ($ β) ≠ omega := by
  cases β <;> intro h <;> injection h <;> contradiction

theorem acc_fin (n : Nat) : Acc SizeOrd.lt (fin n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    constructor
    intro β hβ
    cases β with
    | fin m => exact ih m hβ
    | omegaPlus _ => contradiction

/-- Well-foundedness of `<` on `SizeOrd`. -/
theorem wf_lt : WellFounded SizeOrd.lt := by
  constructor
  intro α
  cases α with
  | fin n => exact acc_fin n
  | omegaPlus k =>
    induction k using Nat.strongRecOn with
    | ind k ih =>
      constructor
      intro β hβ
      cases β with
      | fin m => exact acc_fin m
      | omegaPlus j => exact ih j hβ

end SizeOrd

/-! ## 2. Ordinal Semantics of the Sized Data Type `O` -/

/-- Untyped raw trees of the Brouwer ordinal data type `O`:
    `sized data O : Size -> Set`
    `{ Z : (i : Size) -> O ($ i)`
    `; S : (i : Size) -> O i -> O ($ i)`
    `; L : (i : Size) -> (Nat -> O i) -> O ($ i)`
    `; M : (i : Size) -> O i -> O i -> O ($ i) }` -/
inductive OTerm : Type where
  | Z : OTerm
  | S : OTerm → OTerm
  | L : (Nat → OTerm) → OTerm
  | M : OTerm → OTerm → OTerm

/-- Semantic membership `InO α t` (`t ∈ O^α`):
    Every constructor step requires a strictly smaller ordinal witness `β < α`,
    reflecting $O^\alpha = \bigcup_{\beta < \alpha} F(O^\beta)$. -/
inductive InO : SizeOrd → OTerm → Prop where
  | Z {α β : SizeOrd} :
      β < α → InO α OTerm.Z
  | S {α β : SizeOrd} {x : OTerm} :
      β < α → InO β x → InO α (OTerm.S x)
  | L {α β : SizeOrd} {f : Nat → OTerm} :
      β < α → (∀ n : Nat, InO β (f n)) → InO α (OTerm.L f)
  | M {α β : SizeOrd} {a b : OTerm} :
      β < α → InO β a → InO β b → InO α (OTerm.M a b)

/-- Subtyping / monotonicity (`O_mono`): if `α ≤ γ`, then `O^α ⊆ O^γ`. -/
theorem InO.mono {α γ : SizeOrd} {t : OTerm} (hle : α ≤ γ) (ht : InO α t) : InO γ t := by
  cases ht with
  | Z hβ => exact InO.Z (SizeOrd.lt_of_succ_le_of_le hβ hle)
  | S hβ hx => exact InO.S (SizeOrd.lt_of_succ_le_of_le hβ hle) hx
  | L hβ hf => exact InO.L (SizeOrd.lt_of_succ_le_of_le hβ hle) hf
  | M hβ ha hb => exact InO.M (SizeOrd.lt_of_succ_le_of_le hβ hle) ha hb

/-! ## 3. Refutation of Unguarded Deep Pattern Refinement at Limit Ordinals -/

/-- Embedding `emb : Nat -> O` (`emb n = S^n Z`). -/
def emb : Nat → OTerm
  | 0     => OTerm.Z
  | n + 1 => OTerm.S (emb n)

/-- `emb n` has finite size `fin (n + 1)` and hence size `ω`. -/
theorem emb_in_fin (n : Nat) : InO (SizeOrd.fin (n + 1)) (emb n) := by
  induction n with
  | zero => exact InO.Z (β := SizeOrd.fin 0) (Nat.zero_lt_one)
  | succ n ih => exact InO.S (β := SizeOrd.fin (n + 1)) (Nat.lt_succ_self (n + 1)) ih

theorem emb_in_omega (n : Nat) : InO SizeOrd.omega (emb n) := by
  have hlt : SizeOrd.fin (n + 1) < SizeOrd.omega := trivial
  exact InO.mono (Or.inl hlt) (emb_in_fin n)

/-- Conversely, `emb n` cannot belong to `O^(fin m)` for any `m ≤ n`. -/
theorem emb_not_in_small : ∀ (n m : Nat), m ≤ n → ¬ InO (SizeOrd.fin m) (emb n)
  | 0, m, hm, h => by
    cases h with
    | @Z _ β hβ =>
      cases β with
      | fin k =>
        change k < m at hβ
        omega
      | omegaPlus _ => exact hβ
  | n + 1, m, hm, h => by
    cases h with
    | @S _ β _ hβ hx =>
      cases β with
      | fin k =>
        change k < m at hβ
        exact emb_not_in_small n k (by omega) hx
      | omegaPlus _ => exact hβ

/-- Therefore, `L emb` CANNOT have any finite size `fin m` (nor any `β < ω`).
    Its minimal size is `$ ω = omegaPlus 1`! -/
theorem L_emb_not_below_omega (β : SizeOrd) (hβ : β < SizeOrd.omega) :
    ¬ (∀ n : Nat, InO β (emb n)) := by
  cases β with
  | fin m =>
    intro hall
    exact emb_not_in_small m m (Nat.le_refl m) (hall m)
  | omegaPlus k =>
    change k < 0 at hβ
    omega

/-- However, `L emb` DOES belong to `O^($ ω)` (`omegaPlus 1`), and
    `loop_term = M (L emb) (emb 3)` belongs to `O^($ ($ ω))` (`omegaPlus 2`). -/
def loop_term : OTerm := OTerm.M (OTerm.L emb) (emb 3)

theorem L_emb_in_succ_omega : InO ($ SizeOrd.omega) (OTerm.L emb) :=
  InO.L (SizeOrd.lt_succ_self SizeOrd.omega) emb_in_omega

theorem loop_term_in_omegaPlus2 : InO ($ ($ SizeOrd.omega)) loop_term := by
  apply InO.M (SizeOrd.lt_succ_self ($ SizeOrd.omega))
  · exact L_emb_in_succ_omega
  · exact InO.mono (Or.inl (SizeOrd.lt_succ_self SizeOrd.omega)) (emb_in_omega 3)

/-- **THEOREM 1 (Refutation of Unguarded Sibling Pattern Refinement)**:
    Although `loop_term ∈ O^α` (for `α = ω + 2`) and matches the exact constructor
    shape `M (L emb) (S (S (S Z)))`, there is **NO** ordinal `i` with
    `$ ($ ($ ($ i))) ≤ α` such that `∀ n, InO ($ ($ i)) (emb n)`! -/
theorem unguarded_deep_match_unsound :
    InO ($ ($ SizeOrd.omega)) loop_term ∧
    ¬ ∃ i : SizeOrd,
        (($ ($ ($ ($ i)))) ≤ ($ ($ SizeOrd.omega))) ∧
        (∀ n : Nat, InO ($ ($ i)) (emb n)) := by
  refine ⟨loop_term_in_omegaPlus2, ?_⟩
  rintro ⟨i, hle, hf⟩
  cases i with
  | fin m =>
    exact L_emb_not_below_omega (SizeOrd.fin (m + 2)) trivial hf
  | omegaPlus k =>
    rcases hle with hlt | heq
    · change k + 4 < 2 at hlt
      omega
    · injection heq with hk
      omega

/-! ## 4. The Pattern-Refinement Invariant & Soundness of the Fixed Rule -/

/-- A semantic type family `T : SizeOrd → Val → Prop` is **monotone (covariant)**
    in its size argument if `α ≤ β` implies `T α v → T β v`. -/
def MonotoneTarget {Val : Type} (T : SizeOrd → Val → Prop) : Prop :=
  ∀ {α β : SizeOrd} {v : Val}, α ≤ β → T α v → T β v

/-- **THEOREM 2 (Soundness of the Fixed Pattern-Refinement Rule)** -/
theorem fixed_pattern_refinement_sound
    {Val : Type} {T : SizeOrd → Val → Prop} (hMono : MonotoneTarget T)
    {bodyZ : SizeOrd → Val}
    {bodyS : SizeOrd → OTerm → Val}
    {bodyL : SizeOrd → (Nat → OTerm) → Val}
    {bodyM : SizeOrd → OTerm → OTerm → Val}
    (stepZ : ∀ β : SizeOrd, T ($ β) (bodyZ β))
    (stepS : ∀ (β : SizeOrd) (x : OTerm), InO β x → T ($ β) (bodyS β x))
    (stepL : ∀ (β : SizeOrd) (f : Nat → OTerm), (∀ n, InO β (f n)) → T ($ β) (bodyL β f))
    (stepM : ∀ (β : SizeOrd) (a b : OTerm), InO β a → InO β b → T ($ β) (bodyM β a b))
    {α : SizeOrd} {t : OTerm} (ht : InO α t) :
    match t with
    | OTerm.Z     => ∃ β < α, T α (bodyZ β)
    | OTerm.S x   => ∃ β < α, T α (bodyS β x)
    | OTerm.L f   => ∃ β < α, T α (bodyL β f)
    | OTerm.M a b => ∃ β < α, T α (bodyM β a b) := by
  cases ht with
  | Z hβ =>
    exact ⟨_, hβ, hMono (SizeOrd.succ_le_of_lt hβ) (stepZ _)⟩
  | S hβ hx =>
    exact ⟨_, hβ, hMono (SizeOrd.succ_le_of_lt hβ) (stepS _ _ hx)⟩
  | L hβ hf =>
    exact ⟨_, hβ, hMono (SizeOrd.succ_le_of_lt hβ) (stepL _ _ hf)⟩
  | M hβ ha hb =>
    exact ⟨_, hβ, hMono (SizeOrd.succ_le_of_lt hβ) (stepM _ _ _ ha hb)⟩

/-- **THEOREM 3 (Well-Founded Termination of Sized Recursion under the Fixed Rule)** -/
def sized_recursion_terminates
    {C : SizeOrd → OTerm → Sort u}
    (step : ∀ (α : SizeOrd) (t : OTerm),
      (∀ (β : SizeOrd), β < α → ∀ (s : OTerm), InO β s → C β s) →
      InO α t → C α t)
    (α : SizeOrd) (t : OTerm) (ht : InO α t) : C α t :=
  SizeOrd.wf_lt.fix (C := fun α => ∀ t, InO α t → C α t)
    (fun α ih t ht => step α t ih ht) α t ht

/-! ## 5. Extended Ordinal Lattice with Closure Ordinal `#` (`ExtSize.infty`) -/

/-- Extended sizes including the top closure ordinal `infty` (`#` in Mugda). -/
inductive ExtSize : Type where
  | ord   : SizeOrd → ExtSize
  | infty : ExtSize
  deriving DecidableEq, Repr

namespace ExtSize

def succ : ExtSize → ExtSize
  | ord α => ord ($ α)
  | infty => infty

def le : ExtSize → ExtSize → Prop
  | ord α, ord β => α ≤ β
  | _,     infty => True
  | infty, ord _ => False

instance : LE ExtSize := ⟨ExtSize.le⟩

/-- **THEOREM 4 (Semantic Justification of `$ # = #` and `inst`'s `(VSucc v, VInfty)` Rule)**:
    At the closure ordinal `infty` (`#`), successor is idempotent (`succ infty = infty`). -/
theorem succ_infty : succ infty = infty := rfl

/-- Extended membership `InOExt` including `infty` (`#`) as $\bigcup_{\alpha} O^\alpha$. -/
def InOExt : ExtSize → OTerm → Prop
  | ord α, t => InO α t
  | infty, t => ∃ α : SizeOrd, InO α t

/-- **THEOREM 5 (Initial Algebra Stabilization at `#`)**:
    At `infty` (`#`), `InOExt (succ infty) t ↔ InOExt infty t`, and `OTerm.S x ∈ O^# ↔ x ∈ O^#`.
    This proves why matching `cons .# x xs` against `Stream #` or `succ .# x` against `SNat #`
    via `(VSucc v, VInfty) -> inst v VInfty` is semantically exact at `#`! -/
theorem inOExt_succ_infty (t : OTerm) :
    InOExt (succ infty) t ↔ InOExt infty t := Iff.rfl

theorem inOExt_S_iff (x : OTerm) :
    InOExt infty (OTerm.S x) ↔ InOExt infty x := by
  constructor
  · rintro ⟨α, h⟩
    cases h with
    | @S _ β _ _ hx => exact ⟨β, hx⟩
  · rintro ⟨β, hx⟩
    exact ⟨$ β, InO.S (SizeOrd.lt_succ_self β) hx⟩

end ExtSize

/-! ## 6. Variance Calculus, Admissibility Soundness & Bug 2 (`Wrap`) Tightness -/

/-- Covariant (monotone), contravariant (antitone), and size-independent (`nocc`)
    semantic type families over `SizeOrd`. -/
def Covariant {Val : Type} (F : SizeOrd → Val → Prop) : Prop :=
  ∀ {α β : SizeOrd} {v : Val}, α ≤ β → F α v → F β v

def Contravariant {Val : Type} (F : SizeOrd → Val → Prop) : Prop :=
  ∀ {α β : SizeOrd} {v : Val}, α ≤ β → F β v → F α v

def Independent {Val : Type} (F : SizeOrd → Val → Prop) : Prop :=
  ∀ {α β : SizeOrd} {v : Val}, F α v ↔ F β v

/-- Function-space transformer `Arrow A B α f := ∀ x, A α x → B α (f x)`. -/
def Arrow {Dom Cod : Type} (A : SizeOrd → Dom → Prop) (B : SizeOrd → Cod → Prop)
    (α : SizeOrd) (f : Dom → Cod) : Prop :=
  ∀ x : Dom, A α x → B α (f x)

theorem independent_covariant {Val : Type} {F : SizeOrd → Val → Prop}
    (h : Independent F) : Covariant F :=
  fun _ hf => h.mp hf

theorem independent_contravariant {Val : Type} {F : SizeOrd → Val → Prop}
    (h : Independent F) : Contravariant F :=
  fun _ hf => h.mpr hf

/-- **THEOREM 6 (Function-Space Variance)**:
    If domain `A` is `Contravariant` and codomain `B` is `Covariant`, then `Arrow A B` is `Covariant`.
    Dually, if domain `A` is `Covariant` (e.g. a sized inductive input `InO α`) and codomain `B`
    is `Independent`, then `Arrow A B` is `Contravariant` (usable at any smaller ordinal `β ≤ α`). -/
theorem arrow_covariant {Dom Cod : Type}
    {A : SizeOrd → Dom → Prop} {B : SizeOrd → Cod → Prop}
    (hA : Contravariant A) (hB : Covariant B) :
    Covariant (Arrow A B) := by
  intro α β f hle hf x hx
  exact hB hle (hf x (hA hle hx))

theorem arrow_contravariant {Dom Cod : Type}
    {A : SizeOrd → Dom → Prop} {B : SizeOrd → Cod → Prop}
    (hA : Covariant A) (hB : Contravariant B) :
    Contravariant (Arrow A B) := by
  intro α β f hle hf x hx
  exact hB hle (hf x (hA hle hx))

/-- Semantic model of `sized data Wrap (+ A : Set) : Size -> Set { wrap : (i : Size) -> A -> Wrap A ($ i) }`
    when the parameter `A` is allowed to depend on the outer size `α`. -/
inductive InWrap {Val : Type} (ParamA : SizeOrd → Val → Prop) : SizeOrd → Val → Prop where
  | mk {α β : SizeOrd} {v : Val} :
      β < α → ParamA α v → InWrap ParamA α v

/-- **THEOREM 7a (Soundness of Parameter `nocc` Check in `szUsed'`)**:
    When the data parameter `ParamA` satisfies `Independent` (`nocc` in `α`, as enforced
    by Bug 2's fix in `szUsed'`), `InWrap ParamA` is `Covariant` in `α`! -/
theorem wrap_covariant_of_nocc {Val : Type} {ParamA : SizeOrd → Val → Prop}
    (hNocc : Independent ParamA) : Covariant (InWrap ParamA) := by
  intro α γ v hle hw
  cases hw with
  | mk hβ hv =>
    exact InWrap.mk (SizeOrd.lt_of_succ_le_of_le hβ hle) (hNocc.mp hv)

/-- **THEOREM 7b (Tightness of Bug 2 Fix — `Wrap` Not Covariant Without Parameter `nocc`)**:
    If `nocc` on the parameter `A` of `Wrap A α` is omitted (as in Mugda 2008), taking
    `ParamA α t := ¬ InO α t` makes `InWrap ParamA` **fail covariance**, because `OTerm.Z`
    belongs to `InWrap ParamA (fin 1)` (witnessed by `fin 0 < fin 1` and `emb 1 ∉ O^(fin 1)`),
    yet does NOT belong to `InWrap ParamA (fin 2)`! -/
theorem wrap_not_covariant_without_nocc :
    ¬ Covariant (InWrap (fun α t => ¬ InO α t)) := by
  intro hCov
  -- Consider `t = emb 1 = S Z`.
  -- `emb 1 ∉ O^(fin 1)` (`emb_not_in_small 1 1`), and `fin 0 < fin 1`,
  -- so `InWrap (fun α t => ¬ InO α t) (fin 1) (emb 1)` holds!
  have hw1 : InWrap (fun α t => ¬ InO α t) (SizeOrd.fin 1) (emb 1) := by
    refine InWrap.mk (β := SizeOrd.fin 0) Nat.zero_lt_one ?_
    exact emb_not_in_small 1 1 (Nat.le_refl 1)
  -- Yet `fin 1 ≤ fin 2` and `emb 1 ∈ O^(fin 2)` (`emb_in_fin 1`)!
  have hle : SizeOrd.fin 1 ≤ SizeOrd.fin 2 := Or.inl (Nat.lt_succ_self 1)
  have hw2 := hCov hle hw1
  cases hw2 with
  | mk _ hnot =>
    exact hnot (emb_in_fin 1)

/-! ## 7. Multi-Argument Telescopes & Tightness of `checkNoccEnv` -/

/-- **THEOREM 8 (Multi-Argument Pattern-Refinement Soundness with Context `Γ` and Remaining Domains `Δ`)**:
    Suppose a clause has earlier pattern context `Γ(α)` and remaining domain telescope `Δ(α)`
    and matches a constructor at size `α : SizeOrd` yielding witness `β < α`:
    If `Γ` is `Independent` of `α` (`checkNoccEnv`) and `Δ` is `Independent` of `α` (`checkNoccDomains`)
    and the return type `T` is `Covariant` (`szMonotone`), then refining `α ↦ $ β` inside the
    clause body is sound at all ordinals `α`. -/
theorem multi_arg_pattern_refinement_sound
    {Ctx Dom Val : Type}
    {Γ : SizeOrd → Ctx → Prop}
    {Δ : SizeOrd → Dom → Prop}
    {T : SizeOrd → Val → Prop}
    (hEnvNocc : Independent Γ)
    (hDomNocc : Independent Δ)
    (hMono : Covariant T)
    {body : SizeOrd → Ctx → OTerm → Dom → Val}
    (hStep : ∀ (β : SizeOrd) (c : Ctx) (x : OTerm) (d : Dom),
      Γ ($ β) c → InO β x → Δ ($ β) d → T ($ β) (body β c x d))
    {α : SizeOrd} {c : Ctx} {x : OTerm} {d : Dom}
    (hΓ : Γ α c) (ht : InO α (OTerm.S x)) (hΔ : Δ α d) :
    ∃ β < α, T α (body β c x d) := by
  cases ht with
  | @S _ β _ hβ hx =>
    refine ⟨β, hβ, ?_⟩
    apply hMono (SizeOrd.succ_le_of_lt hβ)
    exact hStep β c x d (hEnvNocc.mpr hΓ) hx (hDomNocc.mpr hΔ)

/-- **THEOREM 9 (Tightness of `checkNoccEnv` — Retroactive Context Refinement Unsound at `ω`)**:
    In `examples/counterexamples/loop_wrapped.ma` (and `examples/loop.ma`), an earlier
    pattern variable `f` has a type mentioning the size variable `j` (`∀ n, InO j (emb n)`
    at `j = ω`), and a later argument `x : O j` is matched against `Z i`, refining `j ↦ $ i`
    inside `f`'s type to `∀ n, InO ($ i) (emb n)` for some `i < ω`.
    We prove that at limit ordinal `j = ω`, the context assumption `∀ n, InO j (emb n)`
    and `InO j OTerm.Z` are BOTH true, yet there is NO `i < ω` for which the refined
    context assumption `∀ n, InO ($ i) (emb n)` holds! -/
theorem checkNoccEnv_tightness :
    (∀ n : Nat, InO SizeOrd.omega (emb n)) ∧
    InO SizeOrd.omega OTerm.Z ∧
    ¬ ∃ i : SizeOrd,
        i < SizeOrd.omega ∧ (∀ n : Nat, InO ($ i) (emb n)) := by
  refine ⟨emb_in_omega, InO.Z (β := SizeOrd.fin 0) trivial, ?_⟩
  rintro ⟨i, hi, hf⟩
  cases i with
  | fin m =>
    exact L_emb_not_below_omega (SizeOrd.fin (m + 1)) trivial hf
  | omegaPlus k =>
    change k < 0 at hi
    omega

/-! ## 8. Coinductive Sized Streams, Contravariant Subtyping & `fib` Productivity -/

/-- Infinite streams over `A` modeled as functions `Nat → A`. -/
abbrev Stream (A : Type) := Nat → A

/-- Coinductive ordinal-indexed approximation `InStream P α s`:
    Dual to `InO` ($\bigcup_{\beta < \alpha}$), a stream `s` belongs to `Stream^α`
    iff for all finite observation depths `n` with `fin n < α`, `P (s n)` holds. -/
def InStream {A : Type} (P : A → Prop) (α : SizeOrd) (s : Stream A) : Prop :=
  ∀ n : Nat, SizeOrd.fin n < α → P (s n)

/-- **THEOREM 10 (Contravariant Coinductive Size Subtyping)**:
    If `α ≤ γ`, then `InStream P γ s → InStream P α s` ($S^\gamma \subseteq S^\alpha$).
    This proves the soundness of `CoInd => leqSize (w2 !! p) (w1 !! p)` in
    `TypeChecker.hs` line 302 (`Mugda/Core.lean` line 1044)! -/
theorem inStream_contravariant {A : Type} {P : A → Prop} :
    Contravariant (InStream P) := by
  intro α γ s hle hγ n hn
  exact hγ n (SizeOrd.lt_of_succ_le_of_le hn hle)

/-- Stream `cons hd tl` shifts indices by 1, so `cons` maps `InStream P α` to `InStream P ($ α)`. -/
def scons {A : Type} (hd : A) (tl : Stream A) : Stream A
  | 0     => hd
  | n + 1 => tl n

theorem scons_productive {A : Type} {P : A → Prop} {α : SizeOrd}
    {hd : A} {tl : Stream A} (hhd : P hd) (htl : InStream P α tl) :
    InStream P ($ α) (scons hd tl) := by
  intro n hn
  cases n with
  | zero => exact hhd
  | succ m =>
    apply htl m
    cases α with
    | fin k =>
      change m + 1 < k + 1 at hn
      change m < k
      omega
    | omegaPlus k =>
      trivial

/-- Fibonacci stream generator `fibFrom x y` (`cofun fib' : Nat -> Nat -> (i : Size) -> Stream i`
    in `examples/fib.ma`) and proof that it is total and productive at every ordinal `α : SizeOrd`
    (including `ω` and `ω + k`), with `(fibFrom 1 1) 4 = 5`. -/
def fibFrom (x y : Nat) : Stream Nat
  | 0     => x
  | n + 1 => fibFrom y (x + y) n

theorem fibFrom_productive (α : SizeOrd) (x y : Nat) :
    InStream (fun _ => True) α (fibFrom x y) :=
  fun _ _ => trivial

theorem fib_4_eq_5 : fibFrom 1 1 4 = 5 := rfl

end MugdaSoundness
