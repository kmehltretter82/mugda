# Mugda Revisited: Sized Types, Size-Change Termination, and the Pattern-Refinement Invariant in Lean 4

**Karl Mehltretter** *(with machine-checked formalization in Constructive Lean 4, 2026)*  
*Original Diploma Thesis: LMU Munich, December 2007 / April 2008 (Advisor: Andreas Abel)*  
📄 **[Download Typeset PDF (`doc/mugda-revisited/mugda-revisited.pdf`)](doc/mugda-revisited/mugda-revisited.pdf)** · 📘 **[Original 2007/2008 Thesis PDF (`doc/da/da.pdf`)](doc/da/da.pdf)**

---

## Abstract

**Mugda** (2007/2008) was, to our knowledge, the first implemented proof assistant to combine **Martin-Löf dependent type theory** and Coquand-style **dependent pattern matching** with **Lee–Jones–Ben-Amram Size-Change Termination (SCT)** (including the nested matrix semiring $\mathsf{ORDER}_+$) and **explicit $\mathsf{Size}$ indices** (`$ i` for successor size and `#` for the closure ordinal $\infty$) to check both **termination** of inductive functions (`fun`) and **productivity** of corecursive definitions (`cofun`).

Eighteen years later, we revisit Mugda through the lens of modern transfinite ordinal semantics and interactive theorem proving:
1. We conduct a complete semantic and algorithmic audit of the 2007/2008 implementation, identifying **six soundness bugs** in the interaction between dependent pattern unification, size subtyping, $\mathsf{ORDER}_+$ matrix comparison, and runtime size erasure.
2. We isolate the exact mathematical root cause of deep pattern-matching unsoundness with sized types (including Cody Roux's limit-ordinal counterexamples): matching an element of a sized inductive family $\mathsf{D}\;\vec{u}\;\alpha$ against a constructor of target type $\mathsf{D}\;\vec{u}\;(\$ i)$ justifies only the **existential ordinal inequality** $\exists \beta < \alpha,\; \$ \beta \le \alpha$, and **not** the syntactic equality $\alpha = \$ \beta$.
3. We formulate and prove the **Pattern-Refinement Invariant** (`checkNoccEnv` + `checkNoccDomains` + parameter `nocc`), showing that substituting $\alpha \mapsto \$ \beta$ during pattern checking is sound at all transfinite ordinals (including limit ordinals $\omega, \omega \cdot 2, \dots$) **if and only if** the refined size variable occurs only in the covariant return type after matching.
4. We port the entire Mugda compiler (~2,400 lines) to the **pure constructive subset of Lean 4** ([`Mugda/Core.lean`](Mugda/Core.lean), with zero `partial`, zero `unsafe`, and zero `sorry`) and verify over 30 semantic and in-place algorithmic metatheorems in [`Mugda/Soundness.lean`](Mugda/Soundness.lean) and [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean).

---

## 1. Introduction

Structural recursion on a single inductive argument—while simple and syntactic—rejects many natural functional programs:
- functions that **permute or swap arguments** (`add2 x (succ y) = succ (add2 y x)`),
- functions that decrease a **lexicographic or nested tuple** (`ack (Pair (succ x) (succ y))`, `addpair`),
- functions where recursion proceeds on the result of a **size-preserving helper** (`div`, `gcd`, `quicksort`, `mergesort`),
- functions that pass a **partially applied recursive call** to a higher-order combinator (`flat` on rose trees via `mapL`), and
- **productive corecursive definitions** (`cofun`) on streams and stream processors (`fib`, `eat`/`ieat`) where corecursive calls appear under continuations or helper functions.

Mugda was designed in 2007/2008 to handle **all five** of these patterns within a single, unified dependent type system by combining two complementary mechanisms:
1. **Syntactic Size-Change Termination (SCT) in $\mathsf{ORDER}_+$:** Call extraction builds call matrices over the nested order algebra $\mathsf{Order} ::= {<} \mid {\le} \mid {?} \mid \mathsf{Mat}(\mathsf{Matrix}\;\mathsf{Order})$, computes the Kleene-star closure under composition, and verifies that every idempotent call matrix $M = M \cdot M$ has a strictly decreasing diagonal entry (`isDecr`).
2. **Semantic Type-Based Termination & Productivity via $\mathsf{Size}$:** Sized inductive types (`sized data D (+ params) : Size -> ... -> Set`) are monotone in their size index (`i <= $ i <= #`), while sized coinductive types (`sized codata C (+ params) : Size -> ... -> Set`) are contravariant (`# <= $ i <= i`).

---

## 2. Transfinite Ordinal Semantics & Why Naive Pattern Unification Fails

### 2.1 Cumulative Ordinal Interpretation of Sized Types

In the transfinite ordinal model (formalized in [`Mugda/Soundness.lean`](Mugda/Soundness.lean) over ordinals $\alpha < \omega \cdot 2$ in `SizeOrd` and extended with the closure ordinal `#` = `ExtSize.infty`), a sized inductive family $\mathsf{D}$ and a sized coinductive family $\mathsf{C}$ are interpreted by transfinite recursion on the ordinal index $\alpha$:

$$\llbracket \mathsf{D}\;\vec{u}\;\alpha \rrbracket = \bigcup_{\beta < \alpha} F_{\mathsf{D}}\!\left(\vec{u},\; \llbracket \mathsf{D}\;\vec{u}\;\beta \rrbracket\right), \qquad \llbracket \mathsf{C}\;\vec{u}\;\alpha \rrbracket = \bigcap_{\beta < \alpha} F_{\mathsf{C}}\!\left(\vec{u},\; \llbracket \mathsf{C}\;\vec{u}\;\beta \rrbracket\right).$$

At the closure ordinal `#` ($\infty$), successor is idempotent (`$ # = #`, proved in [`sinfty_infty`](Mugda/Metatheory.lean#L28) and [`succ_infty`](Mugda/Soundness.lean#L263-L264)), and the inductive interpretation stabilizes as a fixed point ($\llbracket \mathsf{D}\;\vec{u}\;(\$ \infty) \rrbracket = \llbracket \mathsf{D}\;\vec{u}\;\infty \rrbracket$, proved in [`inOExt_S_iff`](Mugda/Soundness.lean#L290-L296)). Moreover, `#` is strictly a top element ($\alpha \le \infty$ for all $\alpha$, with $\infty \not< \infty$), avoiding the $\infty < \infty$ Hurkens-style paradox.

### 2.2 The Limit-Ordinal Gap in Dependent Pattern Matching

In Mugda's dependent pattern checker (`checkPattern`), every constructor of a sized inductive type $\mathsf{D}$ has a return type of the form $\mathsf{D}\;\vec{u}\;(\$ i)$. When a function argument $x : \mathsf{D}\;\vec{u}\;\alpha$ is matched against a constructor pattern $c\,i\,\vec{y}$, the pattern unifier `inst` unifies the expected type $\mathsf{D}\;\vec{u}\;\alpha$ with the constructor's target type $\mathsf{D}\;\vec{u}\;(\$ i)$, producing the substitution:

$$\sigma = [\alpha \mapsto \$ i].$$

In 2008 Mugda, this substitution $\sigma$ was applied **globally** across:
- the types of all previously bound pattern variables in $\Gamma$,
- all remaining argument domains in the clause telescope (and sibling subpatterns of a nested pattern), and
- the clause's return type $T(\alpha)$.

**Why this is unsound at limit ordinals:**
Semantically, knowing $x \in \llbracket \mathsf{D}\;\vec{u}\;\alpha \rrbracket$ guarantees only that there exists some $\beta < \alpha$ such that $x \in F_{\mathsf{D}}(\vec{u}, \llbracket \mathsf{D}\;\vec{u}\;\beta \rrbracket)$. While $\beta < \alpha$ always implies the ordinal inequality $\$ \beta \le \alpha$ ([`succ_le_of_lt`](Mugda/Soundness.lean#L86-L95)), it does **not** imply $\alpha = \$ \beta$ when $\alpha$ is a limit ordinal (such as $\omega$, proved in [`omega_is_limit`](Mugda/Soundness.lean#L105-L106))!

This creates two distinct soundness bugs in unpatched 2008 Mugda:

1. **Bug 1a — Deep Sibling/Multi-Argument Synchronization at $\omega + 2$ ([`cody_simplified.ma`](examples/counterexamples/cody_simplified.ma), [`cody_nowraps.ma`](examples/counterexamples/cody_nowraps.ma)):**
   Consider the Brouwer ordinal type `O : Size -> Set` with constructors `Z`, `S`, `L : (i : Size) -> (Nat -> O i) -> O ($ i)`, and `M : (i : Size) -> O i -> O i -> O ($ i)`.
   At ordinal $\alpha = \omega + 2$, construct:
   - $t_1 = L\;\omega\;(\lambda n.\,S^n\,Z) \in \llbracket O\;(\omega + 1) \rrbracket$ (whose immediate witness is the limit ordinal $\beta_1 = \omega$), and
   - $t_2 = S\;1\;(S\;0\;Z) \in \llbracket O\;2 \rrbracket \subseteq \llbracket O\;(\omega + 1) \rrbracket$ (whose immediate witness is the finite successor ordinal $\beta_2 = 1 = \$ 0$).
   Then $M\;(\omega + 1)\;t_1\;t_2 \in \llbracket O\;(\omega + 2) \rrbracket$.
   However, if a deep pattern `M .($ ($ i)) (L .($ i) f) (S .($ i) (S i z))` matches both children simultaneously, unifying the second child's size with $\$ (\$ i)$ forces the first child's limit ordinal $\beta_1 = \omega$ to equal $\$ i$, which is impossible (`unguarded_deep_match_unsound` in [`Mugda/Soundness.lean`](Mugda/Soundness.lean#L172-L195))!

2. **Bug 1b & Bug 2 — Retroactive Context Refinement & Parameter Smuggling ([`loop_wrapped.ma`](examples/counterexamples/loop_wrapped.ma)):**
   Suppose a function takes `f : SNat j -> Empty` (or hides `SNat j -> Empty` inside a strictly positive parameter of `Wrap (+ A : Set) : Size -> Set`) followed by `x : SNat j`. Matching `x` against `succ i y` produces the substitution $[j \mapsto \$ i]$. Applying $[j \mapsto \$ i]$ retroactively to `f`'s type in $\Gamma$ changes `f : SNat j -> Empty` (a contravariant occurrence of `j`!) into `f : SNat ($ i) -> Empty`, allowing `f` to be applied to `succ i y` itself (`checkNoccEnv_tightness` and `wrap_not_covariant_without_nocc` in [`Mugda/Soundness.lean`](Mugda/Soundness.lean#L350-L397)).

---

## 3. The Pattern-Refinement Invariant

To restore soundness across all transfinite ordinals without sacrificing any intended program from the 2007/2008 thesis, we enforce the **Pattern-Refinement Invariant** whenever pattern unification refines a generic size variable $j$ to a successor size $\$ v$ (`isNewSuccRefinement`):

> **Definition (Pattern-Refinement Invariant):**
> A size refinement $j \mapsto \$ v$ during dependent pattern checking of a pattern $p$ against domain $A$ in context $\Gamma$ with remaining telescope $B$ is admissible if and only if:
> 1. **Context Non-Occurrence (`checkNoccEnv`):** $j$ does not occur free in the type of any earlier pattern variable in $\Gamma$ (`∀ (x, T) ∈ Γ, nocc j T = true`).
> 2. **Remaining Domain Non-Occurrence (`checkNoccDomains`):** $j$ does not occur free in any remaining argument domain of $B$ (including sibling constructor argument domains when checking a constructor pattern `ConP`).
> 3. **Parameter Non-Occurrence (`szUsed'` / `szSizeVarTarget`):** In every sized datatype constructor and admissible function signature, the size variable $i$ does not occur in any datatype parameter `rargs` (`noccList k (.VGen i) rargs = true`).

### Why the Pattern-Refinement Invariant is Both Sound and Tight

- **Soundness ([`fixed_pattern_refinement_sound`](Mugda/Soundness.lean#L211-L220), [`multi_arg_pattern_refinement_sound`](Mugda/Soundness.lean#L372-L384), [`sized_recursion_terminates`](Mugda/Soundness.lean#L230-L239)):**
  When (1)–(3) hold, after matching the pattern $p$, the refined size variable $j$ no longer occurs in $\Gamma$ or in any remaining argument domain of the clause—it can occur **only** in the final target type $R(j)$ of the clause. By function admissibility (`szCheckIndFun`), $R(j)$ is **monotone (covariant)** in $j$. Therefore, for every true semantic witness $\beta < \alpha$:
  $$\beta < \alpha \implies \$ \beta \le \alpha \implies \llbracket R(\$ \beta) \rrbracket \subseteq \llbracket R(\alpha) \rrbracket.$$
  Consequently, checking the clause body against $R(\$ \beta)$ (for an arbitrary fresh size variable $\beta$) soundly establishes $R(\alpha)$ for **every** ordinal $\alpha$, including limit ordinals!
- **Tightness ([`checkNoccEnv_tightness`](Mugda/Soundness.lean#L389-L397), [`wrap_not_covariant_without_nocc`](Mugda/Soundness.lean#L350-L361), [`unguarded_deep_match_unsound`](Mugda/Soundness.lean#L172-L195)):**
  Dropping `checkNoccEnv`, `checkNoccDomains`, or parameter `nocc` immediately admits a machine-checked counterexample in Lean 4.

---

## 4. Algorithmic Fixes in $\mathsf{ORDER}_+$, Call Extraction, Positivity & Size Erasure

In addition to Bugs 1 and 2, our audit and formalization resolved four further bugs in the 2008 implementation:

| Bug | Component | Root Cause in 2008 Mugda | Verified Fix in [`Mugda/Core.lean`](Mugda/Core.lean) & Theorems in [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean) |
|-----|-----------|--------------------------|---------------------------------------------------------------------------------------------------------------------|
| **Bug 3a** | $\mathsf{ORDER}_+$ pattern comparison (`compareExpr`) | `compareExpr` constructed component-wise `.Mat` matrices for multi-argument constructors even when arguments contained `.DotP` or `.SuccP`, fabricating diagonal decreases from inaccessible size dot patterns ([`snat_mat_bug.ma`](examples/counterexamples/snat_mat_bug.ma), [`stree_mat_bug.ma`](examples/counterexamples/stree_mat_bug.ma)). | Restrict `.Mat` construction to pure first-order inductive constructor patterns/arguments (`isPurePatList pl && isPureExprList args`); proved in [`isPurePat_dotP_false`](Mugda/Metatheory.lean#L684) and [`snat_mat_bug_rejected`](Mugda/Metatheory.lean#L748-L749). |
| **Bug 3b** | $\mathsf{ORDER}_+$ semiring (`maxO`, `comp`) | `maxO (Mat m1) (Mat m2)` combined two matrices entrywise (`maxM`), allowing two non-decreasing matrices `[Lt, Un; Un, Un]` and `[Un, Un; Un, Lt]` to sum to `[Lt, Un; Un, Lt]`. | Preserve `.Un` as additive identity and `.Le` as multiplicative identity (so `addpair` and `ack` succeed in [`natpair_source_accepted`](Mugda/Metatheory.lean#L909-L910)), while collapsing when *both* operands of `maxO` are `.Mat` ([`maxO_mat_never_mat`](Mugda/Metatheory.lean#L526-L530), [`collapseOrder_never_mat`](Mugda/Metatheory.lean#L532-L553)). |
| **Bug 4** | Call-graph extraction (`collectCallsExpr`) | `collectCallsExpr` had no case for local `let` expressions (`.LLet x t1 e1 e2`), silently ignoring recursive calls inside `e1` ([`llet_bug.ma`](examples/counterexamples/llet_bug.ma)). | Extract calls from `t1`, `e1`, and `e2`; proved complete in [`collectCalls_llet_includes_bound`](Mugda/Metatheory.lean#L689-L695) and [`llet_bug_rejected`](Mugda/Metatheory.lean#L788-L789). |
| **Bug 5** | Size pattern completeness (`completePatterns`) | `completeFun _ = True` disabled `Completness.hs`, allowing deep size successor patterns `.SuccP (.VarP "i")` that break runtime size erasure (`#`). | Re-enable `completePatterns` on inductive functions (`cp (.SuccP _) = false`). Proved both **universal size-erasure commutation** for complete inductive patterns ([`matchPat_eraseSizes_comm`](Mugda/Metatheory.lean#L211-L264)) and **tightness** ([`succP_breaks_size_erasure`](Mugda/Metatheory.lean#L100-L109)). |
| **Bug 6** | Strict positivity (`sposConstructor`) | `sposConstructor` passed binder depth `0` instead of `k` into `spos`, conflating constructor arguments with datatype parameters. | Thread binder depth `k` through `sposConstructor` ([`Mugda/Core.lean`](Mugda/Core.lean#L508-L522)). |

---

## 5. Constructive Lean 4 Architecture & Machine-Checked Theorems

### 5.1 Why Mugda Fits the Pure Constructive Subset of Lean 4
1. **Strictly Positive First-Order Closures (`Val`):** Mugda represents $\Pi$-types and $\lambda$-abstractions in `Val` via defunctionalized environment closures (`VPi Name Val (List (Name × Val)) Expr` and `VLam Name (List (Name × Val)) Expr`), avoiding negative recursive occurrences of `Val -> Val`.
2. **Pure State + Exception Monad (`TypeCheck`):** Replacing Haskell's `StateT Signature (ErrorT TraceError IO)` with `StateT TCState (Except String)` makes the entire typechecker and evaluator a pure mathematical function inside Lean 4's kernel.
3. **Structural Recursion + Explicit Fuel (`Nat`):** Every pass in [`Mugda/Core.lean`](Mugda/Core.lean) is proved terminating either by direct structural induction or by an explicit `fuel : Nat` parameter—using **zero `partial`**, **zero `unsafe`**, and **zero `sorry`**.

### 5.2 Summary of Machine-Checked Theorems

| Module | Theorem | Mathematical Statement |
|--------|---------|------------------------|
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`SizeOrd.wf_lt`](Mugda/Soundness.lean#L118), [`succ_le_of_lt`](Mugda/Soundness.lean#L86-L95) | Transfinite ordinals below $\omega \cdot 2$ are well-founded and satisfy $\beta < \alpha \implies \$ \beta \le \alpha$. |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`unguarded_deep_match_unsound`](Mugda/Soundness.lean#L172-L195) | Refutes naive deep pattern unification at $\alpha = \omega + 2$ using Cody Roux's ordinal term. |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`fixed_pattern_refinement_sound`](Mugda/Soundness.lean#L211-L220), [`multi_arg_pattern_refinement_sound`](Mugda/Soundness.lean#L372-L384) | Soundness of single- and multi-argument dependent pattern refinement under `checkNoccEnv` + `checkNoccDomains`. |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`sized_recursion_terminates`](Mugda/Soundness.lean#L230-L239) | Well-founded transfinite induction for sized recursive definitions across all ordinals. |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`inOExt_S_iff`](Mugda/Soundness.lean#L290-L296) | Initial algebra stabilization at closure ordinal `#` ($\llbracket O\;(\$ \infty) \rrbracket = \llbracket O\;\infty \rrbracket$). |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`wrap_covariant_of_nocc`](Mugda/Soundness.lean#L337-L343), [`wrap_not_covariant_without_nocc`](Mugda/Soundness.lean#L350-L361) | Soundness and tightness of the Bug 2 parameter `nocc` check on `Wrap (+ A : Set)`. |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`checkNoccEnv_tightness`](Mugda/Soundness.lean#L389-L397) | Tightness of `checkNoccEnv` (retroactive refinement of contravariant context hypotheses). |
| [`Mugda/Soundness.lean`](Mugda/Soundness.lean) | [`inStream_contravariant`](Mugda/Soundness.lean#L416-L420), [`scons_productive`](Mugda/Soundness.lean#L424-L430), [`fibFrom_productive`](Mugda/Soundness.lean#L438-L441) | Contravariant subtyping and productivity of coinductive streams (`Stream #`) and Fibonacci stream. |
| [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean) | [`leqSize_iterVSucc_gen`](Mugda/Metatheory.lean#L59-L64), [`leqSize_iterVSucc_both`](Mugda/Metatheory.lean#L66-L71), [`inst_iterVSucc_infty`](Mugda/Metatheory.lean#L79-L85) | Universal subtyping and unification laws across arbitrary finite successor towers `$^n v`. |
| [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean) | [`matchPat_eraseSizes_comm`](Mugda/Metatheory.lean#L211-L264), [`matchList_eraseSizes_comm`](Mugda/Metatheory.lean#L266-L294), [`succP_breaks_size_erasure`](Mugda/Metatheory.lean#L100-L109) | Universal commutation of `matchPat` with runtime size erasure (`eraseSizesVal`) for complete inductive patterns, plus Bug 5 tightness. |
| [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean) | [`nocc_substVal_id_of_normSizeOrAtom`](Mugda/Metatheory.lean#L345-L392), [`checkNoccEnv_forall_mem`](Mugda/Metatheory.lean#L422-L434), [`checkNoccDomains_pi`](Mugda/Metatheory.lean#L462-L484) | Universal substitution invariance (`nocc` $\implies$ `substVal` is identity) and telescope soundness of `checkNoccEnv` / `checkNoccDomains`. |
| [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean) | [`isDecr_mat_iff`](Mugda/Metatheory.lean#L604-L609), [`checkIdem_sound`](Mugda/Metatheory.lean#L611-L620), [`checkAll_sound`](Mugda/Metatheory.lean#L622-L633) | Universal diagonal witness characterization for `isDecr`, `checkIdem`, and `checkAll`. |
| [`Mugda/Metatheory.lean`](Mugda/Metatheory.lean) | [`compScalar_sound_sizeOrd`](Mugda/Metatheory.lean#L645-L660), [`minScalar_sound_sizeOrd`](Mugda/Metatheory.lean#L662-L667), [`no_infinite_decr_sizeOrd`](Mugda/Metatheory.lean#L669-L679) | Soundness and well-foundedness of `Order` operations with respect to transfinite ordinals `SizeOrd`. |

---

## References

1. **Karl Mehltretter** (2007). *Termination Checking for a Dependently Typed Language*. Diploma thesis, LMU Munich (supervised by Andreas Abel). [`doc/da/da.pdf`](doc/da/da.pdf).
2. **Chin Soon Lee, Neil D. Jones, and Amir M. Ben-Amram** (2001). *The Size-Change Principle for Program Termination*. POPL 2001, pp. 81–92.
3. **Andreas Abel** (2006). *A Polymorphic Lambda-Calculus with Sized Higher-Order Types*. PhD thesis, LMU Munich.
4. **Andreas Abel** (2010). *MiniAgda: Integrating Sized and Dependent Types*. PAR 2010, EPTCS 43, pp. 14–28.
5. **Cody Roux** (2016/2021). *Sized Types and Deep Pattern Matching at Limit Ordinals* (Agda Issues #1946 & #2820).
