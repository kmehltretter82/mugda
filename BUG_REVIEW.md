# Complete Code & Thesis Review of Mugda (2007/2008)

This document presents a comprehensive audit of the **Mugda** language implementation (`*.hs`) and its accompanying Diploma thesis (`doc/da/*.tex`, Karl Mehltretter, LMU Munich, Dec 2007 / Apr 2008, supervised by Andreas Abel).

In addition to reproducing and fixing the famous **deep pattern-matching / limit-ordinal soundness bug** (later analyzed in the setting of MiniAgda/Coq by Cody Roux, Frédéric Blanqui, and Andreas Abel), our audit uncovered and fixed **eight additional bugs** across the type checker, admissibility checker, termination checker, strict positivity checker, completeness checker, example suite, and thesis rules.

A machine-checked **Lean 4 formalization** of the transfinite ordinal semantics, the limit-ordinal counterexample, and the soundness of the fixed pattern-refinement rule is provided in [`formalization/MugdaSoundness.lean`](formalization/MugdaSoundness.lean).

---

## Summary of Bugs Found & Fixed

| # | Component | Severity | Location | Summary | Counterexample / Test |
|---|-----------|----------|----------|---------|-----------------------|
| **1** | Pattern Type-Checking & Unification (`CHKP-CON`) | **Critical (Soundness)** | `TypeChecker.hs` (`checkPattern`), Thesis Fig. 3.6 & §5.6 | Constructor pattern matching refines a flexible size variable $j$ to a successor $\$ s$ by equality substitution across *other* pattern variables in $\Gamma$ or sibling argument domains in $v_B$, which is unsound at limit ordinals $\omega$. | [`cody_simplified.ma`](examples/counterexamples/cody_simplified.ma), [`cody_nowraps.ma`](examples/counterexamples/cody_nowraps.ma), [`loop_wrapped.ma`](examples/counterexamples/loop_wrapped.ma) |
| **2** | Admissibility Check (`szUsed'` & `szSizeVarTarget`) | **Critical (Soundness)** | `TypeChecker.hs` lines 641–648 & 788–800, Thesis Fig. 5.6 & Fig. 5.8 | `szSizeVarDataArgs` checked `nocc` on data type parameters `rargs`, but `szSizeVarTarget` (coinductive target) and `szUsed'` (inductive arguments) omitted the parameter `nocc` check, allowing arbitrary non-admissible types containing $i$ to be smuggled inside a parameter `+ A : Set` of a sized wrapper type `Wrap A i`. | [`loop_wrapped.ma`](examples/counterexamples/loop_wrapped.ma), [`cody_simplified.ma`](examples/counterexamples/cody_simplified.ma) |
| **3** | Extended Matrix Order `ORDER_+` | **Critical (Soundness)** | `Termination.hs` (`comparePattern`, `maxO`), Thesis §4.6 | (a) `comparePattern` built `Mat` matrices for sized constructors and dot patterns `.($ i)`, allowing `isDecr (Mat m) = any isDecr (diag m)` to see `Lt` on a dot-pattern size index while the term argument grew (`Un`). (b) `maxO (Mat m1) (Mat m2)` added subterm matrices entrywise across distinct pattern variables (`BugInMatOrder`). | [`snat_mat_bug.ma`](examples/counterexamples/snat_mat_bug.ma), [`tree_mat_bug.ma`](examples/counterexamples/tree_mat_bug.ma) |
| **4** | Call Extraction for `let`-Expressions | **Critical (Soundness)** | `Termination.hs` line 307 (`collectCalls`) | `Abstract.hs` defines `LLet Name Type Expr Expr` (`let x : t = e1 in e2`), but `collectCalls` matched `LLet _ e1 t1 e2 -> collect e1 ++ collect e2`, inspecting the type annotation instead of the bound expression and ignoring all recursive calls inside `let` bindings! | [`llet_bug.ma`](examples/counterexamples/llet_bug.ma) |
| **5** | Size Pattern Completeness (`completeFun`) | **High (Soundness)** | `Completness.hs` lines 1–12 | `completeFun` was stubbed out to `completeFun _ = True` because an earlier version rejected `DotP`; as a result, the size-pattern completeness check of Thesis Fig. 5.7 (`SuccP` forbidden in `fun`) was completely disabled. | `examples/badadm.ma`, `examples/snat.ma` (`wkSNat2`) |
| **6** | Strict Positivity Checker (`sposConstructor`) | **Medium (Bug)** | `SPos.hs` lines 12–17 | `sposConstructor` called `spos 0 i av` instead of `spos k i av` when traversing the constructor telescope, causing fresh generic values `VGen 0` under nested $\Pi$-types to collide with the first data parameter `VGen 0` (`+ A : Set`) and falsely reject strictly positive constructors. | Positive higher-order parameterized data types |
| **7** | Division Example Syntax (`examples/snat.ma`) | **Medium (Example Bug)** | `examples/snat.ma` lines 56–58 | Wrote `div ($ .i)` (which applies `SuccP` to `DotP`) instead of `div .($ i)` (as written in Thesis §5.4.1 p. 61), causing `examples/snat.ma` to fail at line 56. | [`examples/snat.ma`](examples/snat.ma) |
| **8** | Missing `sized` Keyword in `stree.ma` & `sord.ma` | **Low (Example Bug)** | `examples/stree.ma`, `examples/sord.ma` | Written before the `sized` keyword was made mandatory for sized data declarations (`not a set: Size`). | [`examples/stree.ma`](examples/stree.ma), [`examples/sord.ma`](examples/sord.ma) |
| **9** | Thesis Formula Typos | **Low (Documentation)** | `doc/da/main.tex` line 1636, `concl.tex` line 6 | Line 1636 wrote `\cmp e_1 p_n` instead of `\cmp e_1 p_1` in the first component of constructor comparison; minor typos in `concl.tex`. | [`doc/da/main.tex`](doc/da/main.tex), [`doc/da/concl.tex`](doc/da/concl.tex) |

---

## Detailed Analysis of the Core Soundness Bugs

### 1. The Pattern-Refinement Invariant (Bug 1) and Parameter Smuggling (Bug 2)

#### The Central Question
> *After matching a constructor of a sized inductive type, **which facts about the sizes are semantically justified**, and **why do those facts remain valid through further matching and substitution**?*

#### Semantic Model vs. Syntactic Equality Substitution
In the transfinite ordinal semantics of sized inductive types (formalized in [`formalization/MugdaSoundness.lean`](formalization/MugdaSoundness.lean)), a sized inductive type $\mathsf{D}$ is interpreted as a cumulative hierarchy indexed by ordinals $\alpha$:
$$
  \llbracket \mathsf{D}\;\vec{u}\;\alpha \rrbracket \;=\; \bigcup_{\beta < \alpha} F_{\mathsf{D}}(\vec{u}, \llbracket \mathsf{D}\;\vec{u}\;\beta \rrbracket).
$$
Because $\beta < \alpha \iff \beta + 1 \le \alpha$, this hierarchy enjoys **size subtyping** (monotonicity):
$$
  \alpha \le \alpha' \implies \llbracket \mathsf{D}\;\vec{u}\;\alpha \rrbracket \subseteq \llbracket \mathsf{D}\;\vec{u}\;\alpha' \rrbracket.
$$
Consequently, when a value $v \in \llbracket \mathsf{D}\;\vec{u}\;\alpha \rrbracket$ matches a constructor pattern $c\,i\,\vec{x}$ whose constructor type targets $\mathsf{D}\;\vec{u}\;(\$ i)$, the match **only** justifies the existential witness:
$$
  \exists \beta < \alpha \quad (\text{i.e. } \$ \beta \le \alpha) \quad\text{such that}\quad \vec{x} \in F_c(\vec{u}, \beta).
$$
It does **not** justify the equality $\alpha = \$ \beta$!

#### Why Equality Substitution Fails at Limit Ordinals
Suppose $\alpha$ is a limit ordinal (such as $\omega$) or a small successor of a limit ordinal (such as $\omega + 2$), and $\alpha$ occurs in **two places** in the typing context of a clause:
1. **Cross-branch / cross-argument sharing** ([`cody_simplified.ma`](examples/counterexamples/cody_simplified.ma), [`cody_nowraps.ma`](examples/counterexamples/cody_nowraps.ma)):
   Consider the Brouwer ordinal type $\mathsf{O}$ with constructors:
   - $\mathsf{Z} : (i : \mathsf{Size}) \to \mathsf{O}\;(\$ i)$
   - $\mathsf{S} : (i : \mathsf{Size}) \to \mathsf{O}\;i \to \mathsf{O}\;(\$ i)$
   - $\mathsf{L} : (i : \mathsf{Size}) \to (\mathsf{Nat} \to \mathsf{O}\;i) \to \mathsf{O}\;(\$ i)$
   - $\mathsf{M} : (i : \mathsf{Size}) \to \mathsf{O}\;i \to \mathsf{O}\;i \to \mathsf{O}\;(\$ i)$

   Let $\mathsf{emb}(n) = \mathsf{S}^n(\mathsf{Z}) \in \llbracket \mathsf{O}\;(n+1) \rrbracket \subseteq \llbracket \mathsf{O}\;\omega \rrbracket$.
   Then $\mathsf{L}\;\mathsf{emb}$ has minimal size $\omega + 1$ (since $\sup_{n < \omega} (n+1) = \omega$, which is a limit ordinal), while $\mathsf{emb}(3) = \mathsf{S}(\mathsf{S}(\mathsf{S}(\mathsf{Z})))$ has finite size $4 \le \omega + 1$.
   Therefore, the pair term
   $$
     \mathsf{loop\_term} \;=\; \mathsf{M}(\mathsf{L}\;\mathsf{emb},\; \mathsf{emb}(3)) \;\in\; \llbracket \mathsf{O}\;(\omega + 2) \rrbracket
   $$
   is well-typed at size $\alpha = \omega + 2$.
   However, when matching $\mathsf{loop\_term}$ against the deep pattern
   ```
   M .($ ($ ($ i))) (L .($ ($ i)) f) (S .($ ($ i)) (S .($ i) (S i x)))
   ```
   the right branch `S (S (S x))` has 3 successor constructors, which in Mugda 2008 instantiates the shared size variable of `M`'s children to `$ ($ ($ i))` by **equality substitution**, forcing the left child `L f` to have $f : \mathsf{Nat} \to \mathsf{O}\;(\$ (\$ i))$ for $\omega + 2 \ge \$^4 i$.
   As we prove in `MugdaSoundness.lean` (`unguarded_deep_match_unsound`), **no such ordinal $i$ exists**:
   - If $i = m < \omega$ is finite, then $\$ (\$ i) = m + 2 < \omega$, which cannot bound $\mathsf{emb}(m+2)$.
   - If $i = \omega + k \ge \omega$, then $\$^4 i = \omega + k + 4 > \omega + 2$.

2. **Earlier-variable retroactive refinement + Parameter smuggling** ([`loop_wrapped.ma`](examples/counterexamples/loop_wrapped.ma)):
   In Karl Mehltretter's own 2007 counterexample (`examples/loop.ma`, Thesis Fig. 5.5), `shift_case` and `loop_case` match on a `Maybe (SNat j)` argument after binding a function `f` whose type mentions `j`, retroactively refining `j := $ i` inside `f`'s type.
   While `examples/loop.ma` was rejected by the admissibility check `szCheckIndFun`, wrapping the non-admissible argument in
   ```
   sized data Wrap (+ A : Set) : Size -> Set
   { wrap : (i : Size) -> A -> Wrap A ($ i) }
   ```
   bypassed `szUsed'` in `TypeChecker.hs` (Bug 2) because `szUsed'` forgot to check `nocc` on the parameter `A` of `Wrap A j`!
   Thus [`examples/counterexamples/loop_wrapped.ma`](examples/counterexamples/loop_wrapped.ma) passed Mugda 2008 with zero warnings and looped forever.

#### The Fix: Enforcing the Pattern-Refinement Invariant + Parameter `nocc`
1. **Pattern-Refinement Invariant (`TypeChecker.hs` lines 469–482 & 546–561):**
   Whenever unifying a constructor pattern's return type $v'_c$ against the expected domain $v_A$ in `checkPattern` newly instantiates a flexible size variable $j$ to a successor value `VSucc _`:
   - `checkNoccEnv` verifies that $j$ does **not** occur in the type of any earlier pattern variable in $\Gamma$; and
   - `checkNoccDomains` verifies that $j$ does **not** occur in any remaining argument domain in the telescope $v_B$.

   Why is substituting $j \mapsto \$ i$ in the **return type** $R(j)$ sound when these two conditions hold?
   Because $j$ then occurs after the pattern match *only* in the target type $R(j)$, which by `szCheckIndFun` is **monotone (covariant)** in $j$. Since every semantic witness $i < j$ satisfies $\$ i \le j$, monotonicity yields $\llbracket R(\$ i) \rrbracket \subseteq \llbracket R(j) \rrbracket$ (`fixed_pattern_refinement_sound` in `MugdaSoundness.lean`).

2. **Parameter `nocc` in Admissibility (`TypeChecker.hs` lines 641–648 & 788–800):**
   Added the missing `rargs = take p vl ++ drop (p+1) vl` `nocc` check to both `szSizeVarTarget` and `szUsed'`, matching `szSizeVarDataArgs` and the corrected rules $\mathbf{ind}$ and $\mathbf{coind}$ in Thesis Figures 5.6 and 5.8.

---

### 2. Unsoundness of the Extended Matrix Order `ORDER_+` (Bug 3)

In `Termination.hs` (Thesis Section 4.6), the order `Order = Lt | Eq | Un | Mat (Matrix Order)` was introduced so that nested constructor patterns like `addpair (Pair x (succ y)) = succ (addpair (Pair x y))` in `examples/natpair.ma` could track componentwise decreases before collapsing to a scalar via `collapse m = minO (diag m)`.

Two distinct soundness bugs existed in `ORDER_+`:
1. **Sized & Dot-Pattern Matrix Illusion ([`snat_mat_bug.ma`](examples/counterexamples/snat_mat_bug.ma)):**
   In Mugda, `succ : (i : Size) -> SNat i -> SNat ($ i)` is a **2-argument** constructor whose first argument is a `Size` (erased to `#` at runtime, where `$ # = #`).
   In [`snat_mat_bug.ma`](examples/counterexamples/snat_mat_bug.ma):
   ```
   fun loop : (i : Size) -> SNat i -> SNat i -> SNat #
   { loop .($ ($ ($ i)))
          (succ .($ ($ i)) (succ .($ i) (succ i z)))
          (succ .($ ($ i)) (succ .($ i) w))
     = loop ($ ($ ($ i)))
            (succ ($ i) w)
            (succ ($ ($ i)) (succ ($ i) w))
   ; loop i x y = x
   }
   ```
   When `comparePattern` compared the call argument `succ ($ i) w` against the first pattern `succ .($ ($ i)) (succ .($ i) (succ i z))`, it built a $2 \times 2$ `Mat` whose $(1,1)$ entry compared the size `$ i` against `.($ ($ i))` (`Lt`!) and whose $(2,2)$ entry compared `w` against `succ .($ i) (succ i z)` (`Un`).
   Because `isDecr (Mat m) = any isDecr (diag m)` only checks whether *at least one* diagonal entry is `Lt`, it declared the first argument decreasing even though the actual term argument `w` increased!

2. **Entrywise Matrix Addition Across Different Variables (`maxO (Mat m1) (Mat m2)`, [`tree_mat_bug.ma`](examples/counterexamples/tree_mat_bug.ma)):**
   Even on a pure first-order non-sized binary tree `data Tree : Set { leaf : Tree ; node : Tree -> Tree -> Tree }`, `subterm` used `maxL` (`maxO`) to combine comparisons across all children of a pattern. Because `maxO (Mat m1) (Mat m2)` added matrices entrywise (`zipWith (zipWith maxO)`), a call `g (node x (node y y))` against pattern `node x y` combined `Mat [[Eq, Un], [Un, Un]]` (from `x`) with `Mat [[Un, Un], [Un, Lt]]` (from `y`), allowing the mutual block in [`tree_mat_bug.ma`](examples/counterexamples/tree_mat_bug.ma) to pass termination checking and diverge in a 2-step cycle!

#### The Fix (`Termination.hs` lines 149 & 226–234):
- Restricted `Mat` creation in `comparePattern` to constructors of arity $\ge 2$ whose subpatterns are pure structural patterns (`isPureConP`, containing no `DotP` or `SuccP`, which excludes sized constructors and dot patterns).
- Changed `maxO (Mat m1) (Mat m2)` to collapse both matrices (`maxO (collapse m1) (collapse m2)`) rather than adding matrices entrywise across distinct subterm positions.
- All positive examples using `ORDER_+` (`examples/natpair.ma` `addpair`, `ack`, and `examples/list.ma`) continue to pass, while both [`snat_mat_bug.ma`](examples/counterexamples/snat_mat_bug.ma) and [`tree_mat_bug.ma`](examples/counterexamples/tree_mat_bug.ma) are rejected.

---

### 3. `LLet` Field Order Swap in `Termination.hs` (Bug 4)

In [`Abstract.hs`](Abstract.hs) line 25, local `let`-expressions are defined as:
```haskell
LLet Name Type Expr Expr -- let x : A = e1 in e2
```
And [`TypeChecker.hs`](TypeChecker.hs) line 378 and [`Value.hs`](Value.hs) line 69 both match `LLet x vt e1 e2` with the type `vt` first and the bound expression `e1` second.
However, [`Termination.hs`](Termination.hs) line 307 matched:
```haskell
LLet _ e1 t1 e2 -> collect e1 ++ collect e2
```
This inspected the type annotation `e1` (`Type`) and the body `e2`, completely ignoring the bound expression `t1`! Consequently, the 6-line function in [`examples/counterexamples/llet_bug.ma`](examples/counterexamples/llet_bug.ma):
```
fun loop : Nat -> Nat
{ loop x = let y : Nat = loop x in y }
```
generated an empty call set `[]` in Mugda 2008 and passed termination checking!

#### The Fix (`Termination.hs` line 307):
Changed `LLet _ t1 e1 e2 -> collect t1 ++ collect e1 ++ collect e2`.
