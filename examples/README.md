# Mugda Example Catalog

Every `.ma` file in this directory tree runs in CI. [`tests/golden.sh`](../tests/golden.sh) compares the checker's complete output (stdout, stderr, exit code) against a snapshot in [`tests/expected/`](../tests/expected/). [`tests/js-vs-lean.mjs`](../tests/js-vs-lean.mjs) checks that the browser playground engine reaches the same verdict as the Lean checker. Run both with:

```bash
lake build
make test          # build, axiom audit, accept/reject lists, golden snapshots
make test-js       # playground engine vs Lean checker (needs node)
```

**Exit codes of `.lake/build/bin/mugda`:**

| Exit | Meaning |
|---|---|
| `0` | Accepted with no warnings. |
| `1` + `--- evaluating ---` | Type-correct, but with **warnings** (termination check fails, size pattern incomplete, type not admissible). The functions concerned are not unfolded during evaluation. |
| `1`, no evaluation | **Rejected**: parse error, scope error (both on stderr) or `error during typechecking` (stdout). |

## Directory layout

| Directory | Contents |
|---|---|
| [`tutorial/`](tutorial/) | Example files for the tutorial [*Sized Types with Mugda*](../tutorial/README.md). Each file starts with a `-- Expect: accept` or `-- Expect: reject (…)` header, which the golden runner enforces. |
| [`showcase/`](showcase/) | The larger showcase project ([SizedLib + a verified compiler](showcase/sizedlib/README.md)). |
| [`counterexamples/`](counterexamples/) | Soundness counterexamples to Mugda 2008, all rejected by the fixed checker (see [BUG_REVIEW.md](../BUG_REVIEW.md)). |
| [`adm/`](adm/) | Thesis-era experiments with size admissibility. |
| `*.ma` (top level) | The original 2007/2008 examples from the thesis. Their paths are cited in the thesis, the paper and the Lean docstrings, so they stay where they are. |

> [!NOTE]
> The top-level files are historical. Several predate the `sized` keyword: they declare `data SNat : Size -> Set` without `sized` and are now rejected with `not a set: Size`. Some use syntax that never existed in the released 2008 lexer (`norec`, `nonrec`, the `_` wildcard). They are kept unchanged and listed under *legacy* below. The [tutorial](../tutorial/README.md) teaches the same ideas with current syntax.

## Accepted (exit 0)

| File | What it shows |
|---|---|
| [`acc.ma`](acc.ma) | The accessibility predicate `Acc` and the `<` relation on `Nat` as an inductive family. Also `notLt0`, a function with **no clauses**: Mugda has no coverage checker, so empty functions are accepted (see thesis §"Coverage of pattern matching"). |
| [`addWith.ma`](addWith.ma) | Higher-order `addWith` with **permuted size arguments**. It needs size-change termination *and* sized types together. |
| [`badpos.ma`](badpos.ma) | A strict-positivity playground. The rejected constructors (`Bad1`–`Bad4`, `Bush`) are commented out; uncomment one to see the positivity error. As shipped, only the good declarations remain. |
| [`fib.ma`](fib.ma) | A coinductive sized `Stream`, the Fibonacci stream, a codata predicate `Increasing`, and `eval` of `fib4 = 5`. Used as the running example in the thesis appendix. |
| [`goodterm.ma`](goodterm.ma) | Termination through a higher-order identity function (`Id (zz x)`). |
| [`ho.ma`](ho.ma) | Higher-order functions (`apply neg tt`). Uses `const`, which the Lean port accepts as a synonym for `let`. |
| [`infbranch.ma`](infbranch.ma) | Infinitely branching trees (`node : (Nat -> InfTree A) -> InfTree A`) and `map` through the branching function. |
| [`inverse.ma`](inverse.ma) | Inverting a function with a dot pattern `.(f x)` on the inductive family `Imf`. |
| [`k.ma`](k.ma) | Axiom K is provable by dependent pattern matching (Mugda's matching is K-style). |
| [`nat.ma`](nat.ma) | `Nat`, permuted addition, equality proofs, mutual `even`/`odd`, Ackermann. |
| [`ord.ma`](ord.ma) | Brouwer ordinals and `addord`, terminating by size-change termination through the higher-order subterm `f n`. |
| [`pair.ma`](pair.ma), [`simple.ma`](simple.ma) | Small warm-up programs (`const` definitions, dependent `F : Bool -> Set`). |
| [`procs.ma`](procs.ma) | Sized coinductive processes and oracles, and a coinductive fairness proof (`Inf1`, `proof`). Sized version of `proc.ma`. |
| [`sigma.ma`](sigma.ma) | Dependent pairs and their projections. |
| [`slist.ma`](slist.ma) | Sized lists: mutual `rev`/`rev1`/`rev2` and merge sort (`split`/`merge`/`msort`). Sized version of `list.ma`. |
| [`sord.ma`](sord.ma) | Sized Brouwer ordinals: termination of `addord` follows from sizes alone. |
| [`sort.ma`](sort.ma) | Insertion sort on length-indexed lists (`List A n -> List A n`). |
| [`sp.ma`](sp.ma) | Stream processors in continuation style: an inductive `ISP` inside a coinductive `SP`, with `eat` running a processor on a stream. |
| [`sqsort.ma`](sqsort.ma) | Sized quicksort: `pivot` preserves the size bound `i`. Sized version of `qsort.ma`. |
| [`str.ma`](str.ma) | A stream indexed by `Nat` (not `Size`). The only clause of `zeroes` handles `succ i`: incomplete patterns in a `cofun` are not reported. |
| [`stree.ma`](stree.ma) | Sized rose trees: `flat` through `mapL`, which receives the partially applied `flat i A`. Sized version of `tree.ma`. |
| [`vec.ma`](vec.ma) | Length-indexed vectors with `head`, `tail` and `append : Vec A n -> Vec A m -> Vec A (add n m)`. |

## Accepted with warnings (exit 1, still evaluated)

These files type-check, but the checker flags some functions (named in brackets) and does not unfold them during evaluation. Most are deliberate "before" pictures for a sized "after".

| File | Warning | What it shows |
|---|---|---|
| [`list.ma`](list.ma) | termination [`rev`, `rev2`, `flat`] | The unsized version of `slist.ma`. Without sizes the nested `rev (… rev …)` calls cannot be ordered. |
| [`tree.ma`](tree.ma) | termination [`mapT`, `flat`] | The unsized version of `stree.ma`: recursion through `mapL` is invisible to size-change termination. |
| [`qsort.ma`](qsort.ma) | termination [`qsapp`] | The unsized version of `sqsort.ma`: the lists produced by `pivot` are not known to be smaller. |
| [`crazy.ma`](crazy.ma) | termination [`crazy`] | Permuted arguments with `o2e` in between: not provable by size-change termination without sizes (see legacy `crazys.ma`). |
| [`colist.ma`](colist.ma) | termination [`length`, `length2`] | Unsized colists. `length` of a colist is non-terminating, and `length2` is not guarded. Note the clause typo `length` inside `length2`: clause names are not checked (as in the 2008 parser). |
| [`natpair.ma`](natpair.ma) | termination [`bad`] | `addpair` and `ack` on pairs pass through `ORDER_+` call matrices; the function marked `-- should fail` is rejected as intended. |
| [`snat.ma`](snat.ma) | admissibility + size pattern incomplete [`wkSNat2`] | Sized naturals, `minus`, `div`, `gcd` (all accepted). `wkSNat2` is the deliberate bad example. The `eval` lines show `div 4 4 = 1` and `gcd 6 4 = 2`. |
| [`sum.ma`](sum.ma) | termination [`f`, `g`, `h`] | Mutual recursion through a sum type (`f (succ x) = g (inl x)`): the decrease is hidden inside `inl`. |
| [`perf.ma`](perf.ma) | termination [`f`, `g`] | A performance test: the Wahlstedt 7-function block (`f0`–`f6`) passes, the small mutual `f`/`g`/`h` block does not. |
| [`Trans.ma`](Trans.ma) | termination [`Trans`] | A type-level fixed point `Trans A B = TransMu A B (Trans A B)` is not a terminating definition. |
| [`badterm.ma`](badterm.ma), [`badterm3.ma`](badterm3.ma), [`badterm4.ma`](badterm4.ma) | termination [`f`/`F`] | Minimal non-terminating definitions. |
| [`badterm2.ma`](badterm2.ma) | termination [`div`] | Division by repeated subtraction **without sizes**. Compare with `snat.ma`. |

## Rejected (exit 1, no evaluation)

| File | Error | What it shows |
|---|---|---|
| [`bad1.ma`](bad1.ma), [`bad2.ma`](bad2.ma) | scope | Duplicate identifiers. |
| [`bad3.ma`](bad3.ma), [`badscope4.ma`](badscope4.ma), [`hang.ma`](hang.ma) | scope | Undefined identifiers (in `hang.ma`, `F` is used inside the mutual block before it is in scope). |
| [`badscope.ma`](badscope.ma) | scope | A non-linear pattern. |
| [`badscope2.ma`](badscope2.ma) | scope | A dot pattern `.y` whose variable is never bound. |
| [`badscope5.ma`](badscope5.ma) | scope | Clauses with different numbers of patterns. |
| [`bad4.ma`](bad4.ma), [`bad5.ma`](bad5.ma), [`def.ma`](def.ma) | parse | Syntax errors. |
| [`rose.ma`](rose.ma) | type: not strictly positive | `Rose` through `List` whose parameter is **not** declared `+`. Compare with `badpos.ma`'s `Tree`. |
| [`mut.ma`](mut.ma) | type: `eqVal error` | A function that is ill-typed but would pass the termination check: functions are only unfolded after the whole block has been checked. |
| [`break.ma`](break.ma) | type: cannot infer type | Trying to hide a `Size` quantifier inside a `Set`-valued definition. |
| [`set.ma`](set.ma) | type: not a set | A W-type indexed by `A -> Set`; large indices are not allowed. |
| [`loop.ma`](loop.ma) | type: unsound size refinement | Karl Mehltretter's 2007 counterexample (thesis Fig. 5.5), rejected by the pattern-refinement invariant. |
| [`loop2.ma`](loop2.ma), [`loop3.ma`](loop3.ma) | type | Attempts to hide the bad types of `loop.ma` behind type-level functions. |
| [`stream.ma`](stream.ma) | type: unsound size refinement at `head2` | A collection of sized-stream functions (`zeroes`, `map`, `zipWith`, `nth`, `fib`, `nats`, weakening). The final function, marked `-- bad`, is rejected, which stops the whole file. |
| [`proc.ma`](proc.ma) | type: `eqVal error` at `lemma_ones` | The unsized version of `procs.ma`; the unsized `cofun ones` is not unfolded when comparing types. |
| [`natstream.ma`](natstream.ma) | type: `eqVal error` at `proof` | An unsized coinductive equality proof about `nats`; not accepted. |
| [`counterexamples/*.ma`](counterexamples/) | see [BUG_REVIEW.md](../BUG_REVIEW.md) | Eight soundness counterexamples to Mugda 2008 (`cody_nowraps.ma`, `cody_simplified.ma`, `llet_bug.ma`, `loop_deep.ma`, `loop_wrapped.ma`, `overlap_bug.ma`, `snat_mat_bug.ma`, `stree_mat_bug.ma`). All are rejected (`llet_bug.ma` by the termination check, `overlap_bug.ma` by 3-valued `matchPat`/`eqVal`, and the others by the pattern-refinement invariant). |

### Legacy: stale syntax (rejected for reasons unrelated to their original point)

| File | Current error | Cause |
|---|---|---|
| [`adm/adm1.ma`](adm/adm1.ma), [`adm/adm2.ma`](adm/adm2.ma), [`badadm.ma`](badadm.ma), [`badco.ma`](badco.ma), [`badlist.ma`](badlist.ma), [`crazys.ma`](crazys.ma), [`eqSize.ma`](eqSize.ma), [`inconsistentAssumption.ma`](inconsistentAssumption.ma), [`scolist.ma`](scolist.ma) | `X: not a set: Size` | Written before the `sized` keyword existed (`data SNat : Size -> Set`). With `sized` added, `crazys.ma` is accepted and `badadm.ma`/`adm2.ma` give the intended `size pattern incomplete` warning. |
| [`adm/adm3.ma`](adm/adm3.ma) | parse error | Uses an experimental `norec`/`nonrec` keyword. |
| [`bottomcheck.ma`](bottomcheck.ma) | parse error | Pre-`sized` declaration followed by a malformed clause list. |
| [`subtype.ma`](subtype.ma) | scope: pattern not linear `_` | Mugda has no wildcard pattern; `_` is an ordinary identifier and is used twice. |
| [`sp3.ma`](sp3.ma), [`sp4.ma`](sp4.ma), [`usp.ma`](usp.ma) | scope: mutual combination not supported | Mutual blocks mixing `fun` and `cofun`, which the released checker does not support. `sp.ma` is the supported formulation. |
