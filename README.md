# Mugda — Mini-Agda with Sized Types & Size-Change Termination (Pure Lean 4 Edition)

**Mugda** is a prototype dependently typed functional programming language and proof assistant originally created by **Karl Mehltretter** for his Diploma thesis at **LMU Munich** (December 2007 / April 2008, supervised by **Andreas Abel**), and now ported to and verified in the **pure constructive subset of Lean 4**.

To our knowledge, Mugda was the first implementation to combine:
1. **Martin-Löf dependent type theory** with inductive families and Coquand-style dependent pattern matching (with inaccessible dot patterns `.e`);
2. **The Size-Change Termination (SCT) principle** of Lee, Jones, and Ben-Amram (using call matrices and idempotent completion); and
3. **Explicit `Size` types with subtyping** (`$ i` for size successor and `#` for the closure ordinal $\infty$) to check both **termination** of non-structural recursive functions (such as Euclidean `div`, `gcd`, `quicksort`, `mergesort`, and rose-tree flattening) and **productivity** of corecursive definitions (`cofun` on sized `codata` streams and stream processors).

👉 **[Launch the Interactive Mugda Browser Playground](https://kmehltretter82.github.io/mugda/)** *(runs in your browser with a live toggle between Original 2008 Mugda and Bug-Fixed Mugda)*

---

## Repository History & Tags

This repository preserves the historical Haskell snapshots of Mugda via git tags, while `main` is a **pure Constructive Lean 4 Lake project** containing the verified compiler and its machine-checked metatheory:

| Tag / Branch | Date | Description |
|--------------|------|-------------|
| [`v2007-thesis`](https://github.com/kmehltretter82/mugda/tree/v2007-thesis) | Dec 22, 2007 | Exact untouched Diploma thesis submission snapshot (Haskell). |
| [`v2008-04`](https://github.com/kmehltretter82/mugda/tree/v2008-04) | Apr 20, 2008 | Author's April 2008 cleanup, talk slides (`slides/slides.tex`), and thesis typo fixes. |
| [`v2008-04-ghc9`](https://github.com/kmehltretter82/mugda/tree/v2008-04-ghc9) | Apr 2008 + GHC 9 | Unpatched 2008 Mugda semantics made compilable with modern GHC 9.x (`mugda.cabal`, `Makefile`) + compiled `doc/da/da.pdf`. |
| [`v2026-haskell-fixed`](https://github.com/kmehltretter82/mugda/tree/v2026-haskell-fixed) | 2026 Bug-Fixed Haskell | Bug-fixed Haskell edition (GHC 9.x) prior to transitioning `main` to pure Lean 4. |
| **`main`** | **Pure Constructive Lean 4** | Complete Constructive Lean 4 Lake project ([`Mugda/Core.lean`](Mugda/Core.lean), [`Mugda/Soundness.lean`](Mugda/Soundness.lean), [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean), [`Main.lean`](Main.lean)) with zero `partial`, zero `unsafe`, and zero `sorry`, plus [`examples/`](examples/), [`BUG_REVIEW.md`](BUG_REVIEW.md), [`FORMALIZATION_PLAN.md`](FORMALIZATION_PLAN.md), and the browser playground [`docs/index.html`](docs/index.html). |

---

## Pure Lean 4 Project Structure

| File | Description |
|------|-------------|
| [`lakefile.lean`](lakefile.lean) | Lean 4 Lake build configuration (`lean_lib Mugda` and `lean_exe mugda`). |
| [`Mugda.lean`](Mugda.lean) | Root library module importing `Mugda.Core`, `Mugda.Soundness`, and `Mugda.Metatheory`. |
| [`Mugda/Core.lean`](Mugda/Core.lean) | **Stage I — Executable Constructive Lean 4 Compiler:** 100% total, constructive port of all 13 Mugda compiler modules (`Abstract`, `Completness`, `Value`, `SPos`, `Termination`, `TypeChecker`, `Concrete`, `ScopeChecker`, `Tokens`, `Lexer`, `Parser`) with zero `partial` and zero `sorry`. |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | **Stage II — Semantic Metatheory:** Transfinite ordinal semantics (`SizeOrd`, `ExtSize`), limit-ordinal refutation of Bug 1 (`unguarded_deep_match_unsound`), Pattern-Refinement Invariant soundness (`fixed_pattern_refinement_sound`, `multi_arg_pattern_refinement_sound`), well-founded sized recursion (`sized_recursion_terminates`), initial algebra stabilization (`inOExt_S_iff`), variance calculus & Bug 2 tightness (`wrap_covariant_of_nocc`, `wrap_not_covariant_without_nocc`), `checkNoccEnv_tightness`, and coinductive stream productivity (`inStream_contravariant`, `scons_productive`, `fibFrom_productive`). |
| [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean) | **Stage II — In-Place Algorithmic Verification:** Universal and tightness theorems proved directly on `Mugda.Core`:<br>• **Universal Size-Erasure Commutation (§1–2):** `leqSize_iterVSucc_gen`, `leqSize_iterVSucc_both`, `inst_iterVSucc_infty`, `isIndCompletePat_imp_cp`, `matchPat_eraseSizes_comm`, `matchList_eraseSizes_comm`, and Bug 5 tightness (`succP_breaks_size_erasure`).<br>• **Universal `nocc` & Substitution Invariance (§3):** `nocc_vgen_eq`, `nocc_substVal_id_of_normSizeOrAtom`, `checkNoccEnv_forall_mem`, and `checkNoccDomains_pi`.<br>• **Universal SCT Semiring, Diagonal Witness & Transfinite Ordinal Soundness (§4):** `compScalar_maxScalar_distrib_left/right`, `maxO_mat_never_mat`, `collapseOrder_never_mat`, `isDecr_mat_iff`, `checkIdem_sound`, `checkAll_sound`, `compScalar_sound_sizeOrd`, `minScalar_sound_sizeOrd`, `no_infinite_decr_sizeOrd`, and `collectCalls_llet_includes_bound`.<br>• **End-to-End Kernel Proofs (§5):** `snat_div_source_accepted`, `natpair_source_accepted`, `fib_source_evaluates_to_5`, `cody_nowraps_source_rejected`, `loop_wrapped_rejected`, `snat_mat_bug_rejected`, `llet_bug_rejected`. |
| [`Main.lean`](Main.lean) | Native CLI executable entry point (`lake exe mugda <file.ma>` or `.lake/build/bin/mugda <file.ma>`). |

---

## Building & Running Mugda (Lean 4)

### Prerequisites
- **Lean 4 & Lake** (tested with Lean `4.30.0-nightly` / `4.35.0`; zero external dependencies).

### Build the Library, Proofs & Native CLI Binary
```bash
lake build
# or: make
```

### Run the Test Suite
```bash
make test
```

### Run Mugda on `.ma` Source Files
```bash
.lake/build/bin/mugda examples/fib.ma
.lake/build/bin/mugda examples/snat.ma
.lake/build/bin/mugda examples/sqsort.ma
.lake/build/bin/mugda examples/slist.ma
.lake/build/bin/mugda examples/sp.ma
.lake/build/bin/mugda examples/stree.ma
.lake/build/bin/mugda examples/sord.ma
.lake/build/bin/mugda examples/natpair.ma
```

### Run the Counterexample Suite (All Soundly Rejected)
```bash
.lake/build/bin/mugda examples/counterexamples/loop_wrapped.ma
.lake/build/bin/mugda examples/counterexamples/cody_simplified.ma
.lake/build/bin/mugda examples/counterexamples/cody_nowraps.ma
.lake/build/bin/mugda examples/counterexamples/snat_mat_bug.ma
.lake/build/bin/mugda examples/counterexamples/stree_mat_bug.ma
.lake/build/bin/mugda examples/counterexamples/llet_bug.ma
```

---

## Core Mathematical Result: The Pattern-Refinement Invariant

A central contribution of the modern review ([`BUG_REVIEW.md`](BUG_REVIEW.md) and [`Mugda/Soundness.lean`](Mugda/Soundness.lean)) is a sharp characterization and machine-checked proof of the **Pattern-Refinement Invariant** for dependent pattern matching with sized types:

> **Why naive pattern unification is unsound at limit ordinals:**
> In the ordinal semantics $\llbracket \mathsf{D}\;\vec{u}\;\alpha \rrbracket = \bigcup_{\beta < \alpha} F_{\mathsf{D}}(\vec{u}, \llbracket \mathsf{D}\;\vec{u}\;\beta \rrbracket)$, matching a value $x : \mathsf{D}\;\vec{u}\;\alpha$ against a constructor pattern $c\,i\,\vec{y}$ of target type $\mathsf{D}\;\vec{u}\;(\$ i)$ justifies only the **existential inequality** $\exists \beta < \alpha,\; \$ \beta \le \alpha$, and **not** the equality $\alpha = \$ \beta$.
> When $\alpha$ is a limit ordinal (e.g. $\omega$) or a successor of a limit ordinal (e.g. $\omega + 2$), unifying $\alpha := \$ \beta$ across two sibling branches of a constructor (as in [`cody_simplified.ma`](examples/counterexamples/cody_simplified.ma)) or retroactively into an earlier pattern variable's type (as in [`loop_wrapped.ma`](examples/counterexamples/loop_wrapped.ma)) is semantically false (`unguarded_deep_match_unsound` in [`Mugda/Soundness.lean`](Mugda/Soundness.lean)).

> **The Pattern-Refinement Invariant (`checkNoccEnv` + `checkNoccDomains`):**
> Substituting $\alpha \mapsto \$ \beta$ after matching a constructor is sound **if and only if** the refined size variable $\alpha$:
> 1. does **not** occur in the type of any earlier pattern variable in $\Gamma$ (`checkNoccEnv`), and
> 2. does **not** occur in any remaining argument domain of the clause telescope (`checkNoccDomains`), and
> 3. no non-admissible occurrence of $\alpha$ is hidden inside a data parameter `+ A : Set` (`szUsed'` / `szSizeVarTarget`).
>
> Under this invariant, $\alpha$ occurs after the pattern match *only* in the clause's return type $T(\alpha)$, which is **monotone (covariant)** in $\alpha$. Since $\beta < \alpha \implies \$ \beta \le \alpha$, monotonicity implies $\llbracket T(\$ \beta) \rrbracket \subseteq \llbracket T(\alpha) \rrbracket$, so proving $T(\$ \beta)$ for the constructor's subterms soundly establishes $T(\alpha)$ for **all** ordinals $\alpha$, including limit ordinals (`fixed_pattern_refinement_sound`, `multi_arg_pattern_refinement_sound`, and `sized_recursion_terminates` in [`Mugda/Soundness.lean`](Mugda/Soundness.lean)).

---

## Systematic Evaluation of Expressiveness

The table below evaluates Mugda's termination and productivity checker across five design questions:
1. **What does single-argument structural recursion reject?**
2. **What does the Size-Change Principle (call matrices + `ORDER_+`) add?**
3. **What do explicit `Size` indices and subtyping add beyond syntactic SCT?**
4. **What do the admissibility and pattern-refinement invariants exclude?**
5. **What is the annotation burden on the programmer?**

| Benchmark / Program | File | Structural Recursion | Pure SCT (`Order` / `ORDER_+`) | SCT + `Size` (Mugda) | Mechanism & Annotation Burden |
|---------------------|------|:--------------------:|:------------------------------:|:--------------------:|-------------------------------|
| **Permuted addition** (`add2 x (succ y) = succ (add2 y x)`) | [`nat.ma`](examples/nat.ma) | ❌ | ✅ | ✅ | Off-diagonal call matrix completion; **0 size annotations**. |
| **Mutual `even`/`odd` & Ackermann** | [`nat.ma`](examples/nat.ma), [`natpair.ma`](examples/natpair.ma) | ❌ (single-arg) | ✅ | ✅ | Lexicographic / mutual call-graph completion; **0 size annotations**. |
| **Brouwer ordinal addition** (`addord x (olim f)`) | [`ord.ma`](examples/ord.ma), [`sord.ma`](examples/sord.ma) | ❌ (FO) | ✅ (Axiom 2) | ✅ | Either higher-order subterm $f\,y \le f$ (`ord.ma`) or `Size` decrease (`sord.ma`). |
| **Nested pair addition** (`addpair (Pair x (succ y))`) | [`natpair.ma`](examples/natpair.ma) | ❌ | ✅ (`ORDER_+`) | ✅ | Matrix-valued entry in `ORDER_+` tracks components of `Pair`; **0 size annotations**. |
| **Euclidean `div` & `gcd`** | [`snat.ma`](examples/snat.ma) | ❌ | ❌ | ✅ | `minus : (i : Size) -> SNat i -> SNat # -> SNat i` preserves upper bound `i`; **1 `Size` parameter per recursive fun**. |
| **Quicksort & Mergesort** | [`sqsort.ma`](examples/sqsort.ma), [`slist.ma`](examples/slist.ma) | ❌ | ❌ | ✅ | `pivot` / `split` preserve `SList A i` upper bound via subtyping; **1 `Size` parameter + dot pattern `.($ i)`**. |
| **Rose-tree flattening** (`flat` via `mapL`) | [`stree.ma`](examples/stree.ma) | ❌ | ❌ | ✅ | Higher-order `mapL # (Tree A i) ... (flat i A) l` passes partially applied `flat i A` with strictly smaller size `i < $ i`. |
| **Permuted higher-order `addWith`** | [`addWith.ma`](examples/addWith.ma) | ❌ | ❌ | ✅ | Requires **both** SCT (permuting `i` and `j`) **and** `Size` (`f : (k : Size) -> SNat k -> SNat k`). |
| **Coinductive streams (`zeroes`, `fib`, `zipWith`)** | [`fib.ma`](examples/fib.ma), [`stream.ma`](examples/stream.ma) | Guarded only | ❌ | ✅ | Dual corecursion on size `($ i) -> i`; `head`/`tail` total on `Stream #`. |
| **Stream processor `eat` (CPS under `ieat`)** | [`sp.ma`](examples/sp.ma) | ❌ (unguarded) | ❌ | ✅ | Corecursive call `eat i` is inside continuation passed to `ieat` (rejected by syntactic guardedness, accepted by `Size`). |
| **Haskell `fib = 1 : 1 : zipWith (+) fib (tail fib)`** | [`stream.ma`](examples/stream.ma) | ❌ | ❌ | 🚫 Rejected | Requires `tail : (i : Size) -> Stream ($ i) -> Stream i`, which violates coinductive admissibility (and diverges under Mugda's eager constructor arguments). |
| **Deep sibling match at limit ordinal $\omega$** | [`cody_simplified.ma`](examples/counterexamples/cody_simplified.ma) | ❌ | ❌ | 🚫 Rejected | Violates the **Pattern-Refinement Invariant** (`checkNoccDomains`) and parameter admissibility (`szUsed'`). |
