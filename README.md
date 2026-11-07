# Mugda — Mini-Agda with Sized Types & Size-Change Termination

**Mugda** is a prototype dependently typed functional programming language and proof assistant created by **Karl Mehltretter** for his Diploma thesis at **LMU Munich** (December 2007 / April 2008, supervised by **Andreas Abel**).

To our knowledge, Mugda was the first implementation to combine:
1. **Martin-Löf dependent type theory** with inductive families and Coquand-style dependent pattern matching (with inaccessible dot patterns `.e`);
2. **The Size-Change Termination (SCT) principle** of Lee, Jones, and Ben-Amram (using call matrices and idempotent completion); and
3. **Explicit `Size` types with subtyping** (`$ i` for size successor and `#` for the closure ordinal $\infty$) to check both **termination** of non-structural recursive functions (such as Euclidean `div`, `gcd`, `quicksort`, `mergesort`, and rose-tree flattening) and **productivity** of corecursive definitions (`cofun` on sized `codata` streams and stream processors).

👉 **[Launch the Interactive Mugda Browser Playground](https://kmehltretter82.github.io/mugda/)** *(runs in your browser with a live toggle between Original 2008 Mugda and Bug-Fixed Mugda)*

---

## Repository History & Tags

This repository preserves the historical snapshots of Mugda alongside the modernized, bug-fixed edition:

| Tag / Branch | Date | Description |
|--------------|------|-------------|
| [`v2007-thesis`](https://github.com/kmehltretter82/mugda/tree/v2007-thesis) | Dec 22, 2007 | Exact untouched Diploma thesis submission snapshot. |
| [`v2008-04`](https://github.com/kmehltretter82/mugda/tree/v2008-04) | Apr 20, 2008 | Author's April 2008 cleanup, talk slides (`slides/slides.tex`), and thesis typo fixes. |
| [`v2008-04-ghc9`](https://github.com/kmehltretter82/mugda/tree/v2008-04-ghc9) | Apr 2008 + GHC 9 | Unpatched 2008 Mugda semantics made compilable with modern GHC 9.x (`mugda.cabal`, `Makefile`) + compiled `doc/da/da.pdf`. |
| **`main`** | Modern Bug-Fixed | Fixes all 9 soundness and implementation bugs found during the complete code & thesis audit, adds [`examples/counterexamples/`](examples/counterexamples/), the Lean 4 soundness proof [`formalization/MugdaSoundness.lean`](formalization/MugdaSoundness.lean), [`FORMALIZATION_PLAN.md`](FORMALIZATION_PLAN.md), [`BUG_REVIEW.md`](BUG_REVIEW.md), and the browser playground [`docs/index.html`](docs/index.html). |

---

## Building & Running Mugda

### Prerequisites
- **GHC** (tested with GHC 9.14.1; any GHC $\ge 8.10$ works out of the box with zero external Hackage dependencies beyond `base` and `mtl`).
- *(Optional)* **Lean 4** to verify the machine-checked soundness and counterexample proofs in [`formalization/MugdaSoundness.lean`](formalization/MugdaSoundness.lean).

### Build with `make` or `cabal`
```bash
make
# or: cabal build
```

### Run Examples
```bash
./Main examples/fib.ma
./Main examples/snat.ma
./Main examples/sqsort.ma
./Main examples/slist.ma
./Main examples/sp.ma
./Main examples/stree.ma
```

### Run the Counterexample Suite
```bash
./Main examples/counterexamples/loop_wrapped.ma
./Main examples/counterexamples/cody_simplified.ma
./Main examples/counterexamples/cody_nowraps.ma
./Main examples/counterexamples/snat_mat_bug.ma
./Main examples/counterexamples/stree_mat_bug.ma
./Main examples/counterexamples/llet_bug.ma
```

### Verify the Lean 4 Soundness Proof
```bash
lean formalization/MugdaSoundness.lean
```

---

## Core Mathematical Result: The Pattern-Refinement Invariant

A central contribution of the modern review ([`BUG_REVIEW.md`](BUG_REVIEW.md) and [`formalization/MugdaSoundness.lean`](formalization/MugdaSoundness.lean)) is a sharp characterization and machine-checked proof of the **Pattern-Refinement Invariant** for dependent pattern matching with sized types:

> **Why naive pattern unification is unsound at limit ordinals:**
> In the ordinal semantics $\llbracket \mathsf{D}\;\vec{u}\;\alpha \rrbracket = \bigcup_{\beta < \alpha} F_{\mathsf{D}}(\vec{u}, \llbracket \mathsf{D}\;\vec{u}\;\beta \rrbracket)$, matching a value $x : \mathsf{D}\;\vec{u}\;\alpha$ against a constructor pattern $c\,i\,\vec{y}$ of target type $\mathsf{D}\;\vec{u}\;(\$ i)$ justifies only the **existential inequality** $\exists \beta < \alpha,\; \$ \beta \le \alpha$, and **not** the equality $\alpha = \$ \beta$.
> When $\alpha$ is a limit ordinal (e.g. $\omega$) or a successor of a limit ordinal (e.g. $\omega + 2$), unifying $\alpha := \$ \beta$ across two sibling branches of a constructor (as in [`cody_simplified.ma`](examples/counterexamples/cody_simplified.ma)) or retroactively into an earlier pattern variable's type (as in [`loop_wrapped.ma`](examples/counterexamples/loop_wrapped.ma)) is semantically false (`unguarded_deep_match_unsound` in [`MugdaSoundness.lean`](formalization/MugdaSoundness.lean)).

> **The Pattern-Refinement Invariant (`checkNoccEnv` + `checkNoccDomains`):**
> Substituting $\alpha \mapsto \$ \beta$ after matching a constructor is sound **if and only if** the refined size variable $\alpha$:
> 1. does **not** occur in the type of any earlier pattern variable in $\Gamma$ (`checkNoccEnv`), and
> 2. does **not** occur in any remaining argument domain of the clause telescope (`checkNoccDomains`), and
> 3. no non-admissible occurrence of $\alpha$ is hidden inside a data parameter `+ A : Set` (`szUsed'` / `szSizeVarTarget`).
>
> Under this invariant, $\alpha$ occurs after the pattern match *only* in the clause's return type $T(\alpha)$, which is **monotone (covariant)** in $\alpha$. Since $\beta < \alpha \implies \$ \beta \le \alpha$, monotonicity implies $\llbracket T(\$ \beta) \rrbracket \subseteq \llbracket T(\alpha) \rrbracket$, so proving $T(\$ \beta)$ for the constructor's subterms soundly establishes $T(\alpha)$ for **all** ordinals $\alpha$, including limit ordinals (`fixed_pattern_refinement_sound` and `sized_recursion_terminates` in [`MugdaSoundness.lean`](formalization/MugdaSoundness.lean)).

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
