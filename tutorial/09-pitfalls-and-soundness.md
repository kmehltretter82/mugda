# Chapter 9: Pitfalls, Counterexamples & Soundness

[**← Chapter 8: Mixing Induction & Coinduction**](./08-mixing-induction-and-coinduction.md) | [**Table of Contents**](./README.md)

---

## 1. Why Sized Type Checkers Must Be Designed with Extreme Care

Sized types give you remarkable expressive power: Euclidean division, mergesort, quicksort, Rose tree folds, Fibonacci streams, and mixed inductive/coinductive stream processors all type-check cleanly without manual fuel arguments or accessibility proofs.

However, integrating sized types with **dependent pattern matching** and **limit ordinals (`#` / $\infty$)** is notoriously subtle. If a type checker allows a pattern match to unify or refine a size variable in the wrong scope, or if evaluation of open terms falls through a stuck clause, you can trick the checker into accepting a non-terminating function or proving `False`!

In this final chapter, we tour the **four soundness boundaries** of Mugda, run the concrete counterexample files in `examples/tutorial/` and `examples/counterexamples/`, and connect each rule directly to the machine-checked theorems in [`Mugda/Soundness.lean`](../../Mugda/Soundness.lean) and [`Mugda/Metatheory.lean`](../../Mugda/Metatheory.lean).

---

## 2. Boundary 1: Size Patterns (`($ i)`) and Admissibility (`admissible`)

In Chapter 7, we wrote coinductive functions by matching on a successor size pattern `($ i)` on the left-hand side:

```mugda
cofun repeat : (A : Set) -> A -> (i : Size) -> Stream A i
{
  repeat A a ($ i) = scons A i a (repeat A a i)
}
```

Why is matching on `($ i)` sound when producing a coinductive `Stream A i`, yet **unsound** in an inductive `fun` or when producing an inductive type?

Semantically, matching a size variable `i : Size` against `($ i)` is **transfinite induction on ordinals**:
- At successor ordinals $\alpha + 1$, the clause builds step $\alpha + 1$ from step $\alpha$.
- At the **limit ordinal `#` ($\infty$)**, a family $T(i)$ that holds for all $i < \lambda$ extends to $T(\lambda)$ if and only if $T(i)$ is **upward-closed at limits** ($\bigcap_{i < \lambda} T(i) \subseteq T(\lambda)$), which in Mugda means **$i$ must occur contravariantly (`-Size`) in the target type $T(i)$** (and not positively in any later domain of the telescope).

### Try It: `09_incomplete_size_bad.ma` and `09_inadmissible_bad.ma`

Run Mugda on [`examples/tutorial/09_incomplete_size_bad.ma`](../../examples/tutorial/09_incomplete_size_bad.ma) and [`examples/tutorial/09_inadmissible_bad.ma`](../../examples/tutorial/09_inadmissible_bad.ma):

```bash
./.lake/build/bin/mugda examples/tutorial/09_incomplete_size_bad.ma
./.lake/build/bin/mugda examples/tutorial/09_inadmissible_bad.ma
```

- In `09_incomplete_size_bad.ma`, an ordinary `fun` attempts to match on `($ i)`: Mugda rejects it with `size pattern incomplete`.
- In `09_inadmissible_bad.ma`, a `cofun` matches on `($ i)` while returning a covariant `SNat i` instead of a contravariant `codata`: Mugda rejects it with `type of cofun not admissible`.

In [`Mugda/Metatheory.lean`](../../Mugda/Metatheory.lean), the theorem `admissible_vpi_inv` proves universally that `admissible` succeeds on a telescope $\Delta \to T$ if and only if at least one `SuccP`-bound size variable occurs negatively (`nocc` returns `.Just .Neg`) in $T$ and no `SuccP`-bound variable occurs positively in any remaining domain of $\Delta$.

---

## 3. Boundary 2: The Pattern-Refinement Invariant (`checkNoccEnv` & `checkNoccDomains`)

Now comes the deepest subtlety in combining dependent pattern matching with sized types — first exposed at limit ordinal $\omega$ by Karl Mehltretter's 2007 counterexample (`examples/loop.ma`, thesis Fig. 5.5) and generalized to higher limit ordinals ($\omega + 2$) during the 2026 Lean 4 verification (documented in [`BUG_REVIEW.md`](../../BUG_REVIEW.md) and [`MUGDA_REVISITED.md`](../../MUGDA_REVISITED.md)).

Wait: even in an ordinary `fun` (where raw `($ i)` patterns are forbidden!), a constructor pattern still refines a size index via a dot pattern `.($ i)`:

```mugda
sized data O : Size -> Set {
  Z : (i : Size) -> O ($ i) ;
  S : (i : Size) -> O i -> O ($ i) ;
  L : (i : Size) -> (Nat -> O i) -> O ($ i)
}

fun stepCount : (i : Size) -> O i -> Nat {
  stepCount .($ i) (Z i)   = zero ;
  stepCount .($ i) (S i x) = succ (stepCount i x) ;
  stepCount .($ i) (L i f) = succ (stepCount i (f zero))
}
```

In [`examples/tutorial/09_soundness_ok.ma`](../../examples/tutorial/09_soundness_ok.ma), `stepCount` peels **one** constructor layer off `O i`, refining the size parameter to `.($ i)`. Why is this completely sound, even at `#`?
Because `O` is covariant (`+Size`) and continuity at limit ordinal $\infty$ guarantees $O^\infty = \bigcup_{\alpha < \infty} O^{\alpha + 1}$: every single value of `O #` was constructed by `Z`, `S`, or `L` at some predecessor size!

**When does constructor size refinement become UNSOUND?**

When **two** patterns (either two sibling arguments in a telescope, or a deep nested pattern inside a constructor that shares a size variable across two branches) force the **same** size variable `i` to be a successor `($ i)` simultaneously!

### Try It: `09_deep_limit_bad.ma`

Open [`examples/tutorial/09_deep_limit_bad.ma`](../../examples/tutorial/09_deep_limit_bad.ma):

```mugda
sized data O : Size -> Set {
  Z : (i : Size) -> O ($ i) ;
  S : (i : Size) -> O i -> O ($ i) ;
  L : (i : Size) -> (Nat -> O i) -> O ($ i) ;
  P : (i : Size) -> O i -> O i -> O ($ i)
}

fun deepLoop : (i : Size) -> O i -> Nat {
  deepLoop .($ ($ i)) (P .($ i) (S i x) (L i f)) =
    deepLoop ($ i) (P i x (f zero))
}
```

Look closely at what `deepLoop` tries to do:
1. The constructor `P : (i : Size) -> O i -> O i -> O ($ i)` pairs two ordinals of the **same** size bound `i`.
2. Inside `(P .($ i) (S i x) (L i f))`, the first child `(S i x)` refines the shared size `.($ i)` of `P` so that the second child `(L i f)` must also have size `($ i)` (making `f : Nat -> O i` for the *same* predecessor `i`)!
3. Why does that fail at limit ordinal $\omega + 2$ (`#`)?
   - Consider the limit ordinal $l = \text{L } \#\ \text{emb} \in O^{\omega + 1}$, where $\text{emb } n \in O^{n+1}$ embeds every natural number $n$ into `O`.
   - Each $\text{emb } n$ has finite size $n + 1 < \omega$, so $l = \text{L } \#\ \text{emb}$ has size $\omega + 1$.
   - Now pair $s = \text{S } \#\ l \in O^{\omega + 2}$ with $l \in O^{\omega + 1} \subseteq O^{\omega + 2}$ inside `P # s l`!
   - If `deepLoop` were accepted, matching `P # (S # l) (L # emb)` against `P .($ i) (S i x) (L i f)` would bind `x = l` and `f = emb` at a common size `i` below $\omega + 1$, and then call `deepLoop ($ i) (P i l (emb zero))` — which loops forever if `f` returns `s`!

Run Mugda on [`examples/tutorial/09_deep_limit_bad.ma`](../../examples/tutorial/09_deep_limit_bad.ma):

```bash
./.lake/build/bin/mugda examples/tutorial/09_deep_limit_bad.ma
```

Output:
```text
deepLoop: variable i0 occurs negatively in remaining domain O i0
```

### How Mugda's Pattern-Refinement Invariant Blocks It

In [`Mugda/Core.lean`](../../Mugda/Core.lean), whenever `checkPattern` checks a constructor pattern `.ConP`:
1. **`checkNoccEnv`:** None of the constructor-bound variables may occur negatively (`-` or invariant `o`) in the already-bound pattern environment $\rho$.
2. **`checkNoccDomains`:** None of the constructor-bound variables may occur negatively (`-` or invariant `o`) in the **remaining telescope domains** of the clause (including sibling constructor arguments!).
3. **Datatype Parameter `nocc`:** Parameters before `:` in `data D (A : P) : ...` must respect their declared variance in all constructor arguments.

In [`Mugda/Soundness.lean`](../../Mugda/Soundness.lean), both directions are machine-checked in Lean 4:
- **`soundness_theorem`:** Every clause accepted by `checkPattern` satisfies `SoundClauseRefinement`.
- **`tightness_theorem` (`bug1_rejected`, `bug2_rejected`, `bug3_rejected`):** Disabling any one of the three checks immediately admits a counterexample.

---

## 4. Boundary 3: Overlapping Clauses & 3-Valued Pattern Matching (`09_overlap_bad.ma`)

A third soundness boundary concerns **open evaluation during dependent type checking** when a function has **overlapping clauses** (a catch-all variable pattern after a constructor pattern).

Open [`examples/tutorial/09_overlap_bad.ma`](../../examples/tutorial/09_overlap_bad.ma):

```mugda
fun isz : Nat -> Bool {
  isz zero = tt ;
  isz x    = ff
}

fun bad : (n : Nat) -> Eq Bool (isz n) ff {
  bad n = refl Bool ff
}
```

On closed numbers, `isz zero` reduces to `tt` and `isz (succ zero)` reduces to `ff`.
What should `isz n` reduce to when `n : Nat` is a **free variable** (a neutral value `.VGen 0` while type-checking `bad`)?

- In the original 2008 Haskell implementation (`Value.hs`), `match` returned a 2-valued `Maybe Env` (`Just env` or `Nothing`), conflating:
  - **Definite constructor mismatch** (`zero` vs `succ y` $\to$ advance to Clause 2), and
  - **Indeterminate / stuck match on a neutral variable** (`zero` vs `.VGen 0` $\to$ must block!).
- Because `match` returned `Nothing` on `zero` vs `.VGen 0`, `matchClauses` fell through Clause 1 and reduced `isz n` to `ff` via Clause 2 (`isz x = ff`)! That allowed `bad (n : Nat) : Eq Bool (isz n) ff = refl Bool ff` to type-check, and `bad zero : Eq Bool tt ff` proved `tt = ff`!

### How Lean 4 Mugda Fixes It (`MatchResult`: `matched` | `mismatch` | `stuck`)

In [`Mugda/Core.lean`](../../Mugda/Core.lean), `matchPat`, `matchList`, and `matchClause` return a **3-valued** `MatchResult Env`:

```lean
inductive MatchResult (α : Type) where
  | matched  : α → MatchResult α
  | mismatch : MatchResult α
  | stuck    : MatchResult α
```

- When a constructor pattern (`ConP`) or successor pattern (`SuccP`) inspects a distinct constructor (`c ≠ c'`), it returns `.mismatch`, and `matchClauses` advances to the next clause.
- When a constructor pattern or successor pattern inspects a neutral variable (`.VGen k`) or unforced neutral application, it returns `.stuck`, and **`matchClauses` halts immediately**!

Run Mugda on [`examples/tutorial/09_overlap_bad.ma`](../../examples/tutorial/09_overlap_bad.ma):

```bash
./.lake/build/bin/mugda examples/tutorial/09_overlap_bad.ma
```

Output:
```text
bad: eqVal error: VApp (VFun isz ... [VGen 0]) != VCon ff []
```

Because `isz n` is stuck on the neutral variable `n` (`VGen 0`), it remains `VApp (VFun isz ...) [VGen 0]`, which is not definitionally equal to `ff`!

In [`Mugda/Metatheory.lean`](../../Mugda/Metatheory.lean) (§2B), the machine-checked theorems `matchClauses_stuck_blocks_fallthrough`, `matchClauses_mismatch_advances`, and `matchClauses_conP_vgen_never_falls_through` prove universally that neutral scrutinees never fall through a constructor pattern into a subsequent clause.

---

## 5. Boundary 4: Exhaustive Pattern Coverage

One final design note to keep in mind when writing proofs in Mugda:
- Following MiniAgda 2008 (thesis §"Coverage of pattern matching"), Mugda checks termination (`Termination.lean`), strict positivity (`spos`), size variance (`checkData`), pattern refinement (`checkNoccEnv`/`checkNoccDomains`), and 3-valued reduction (`MatchResult`), **but does not include an automated exhaustiveness / coverage checker** for `fun` clauses.
- If you omit a constructor case (for example, writing a `fun` on `Nat` with a clause for `succ n` and no clause for `zero`), evaluating that function on `zero` simply gets stuck (returns a neutral `VApp`), so evaluation and type checking never crash or loop; however, when using Mugda as a proof assistant, an empty function `fun f : Nat -> Empty {}` with zero clauses would trivially inhabit `Nat -> Empty`.
- **Rule of thumb when writing proofs in Mugda:** Always write one clause for every constructor of an inductive type (except uninhabited types like `Empty`, which legitimately have zero constructors).

---

## 6. Where to Go Next

Congratulations on completing the **Sized Types with Mugda** tutorial! Here is where to explore next:

1. **The Showcase Project (`SizedLib` + Verified Expression Compiler):**
   - Read [`examples/showcase/sizedlib/README.md`](../../examples/showcase/sizedlib/README.md) and inspect [`examples/showcase/sizedlib/sizedlib.ma`](../../examples/showcase/sizedlib/sizedlib.ma) — a ~1,100-line verified library combining sized arithmetic (`div`, `mod`, `gcd`), sorting (`mergeSort`, `quickSort`), Rose trees, infinite streams (`fibs`, `hamming`), mixed stream processors, and a **verified stack-machine compiler with constant-folding optimization (`compile_correct`, `compileOpt_correct`)**.
2. **The Machine-Checked Metatheory in Lean 4:**
   - Browse [`Mugda/Soundness.lean`](../../Mugda/Soundness.lean) and [`Mugda/Metatheory.lean`](../../Mugda/Metatheory.lean) to see how every pass of the Mugda type checker is specified and verified in Lean 4 with zero `sorry` and zero `partial`.
3. **The Interactive Web Playground:**
   - Open `docs/index.html` (or the live GitHub Pages site) to experiment with Mugda programs in your browser and toggle between **2026 Fixed (Sound)** and **2008 Original (Buggy)** modes!

---

[**← Chapter 8: Mixing Induction & Coinduction**](./08-mixing-induction-and-coinduction.md) | [**Table of Contents**](./README.md)
