# SizedLib: a small library and a verified compiler in Mugda

SizedLib is the largest program written in Mugda so far: about 1,200 lines in
one file. It shows what the language can do in practice:

- **Sized types** let the checker accept recursion that is not structural
  (division, Euclid's algorithm, quicksort, merge sort, rose trees).
- **Sized coinductive types** give productive streams, stream processors and
  coinductive bisimulation proofs.
- **Dependent types with pattern matching** let us prove a compiler from
  arithmetic expressions to a stack machine correct.

The whole program passes the Lean 4 checker with no warnings (exit code 0) in
about 0.03 s.

## Layout

| File | Purpose |
|------|---------|
| `src/00_header.ma` … `src/04_compiler.ma` | The program, split into parts. Edit these. |
| `sizedlib.ma` | **Generated**: the parts concatenated in filename order. Mugda has no imports, so this is the file that gets checked. Do not edit it by hand. |
| `bad/*.ma` | Small standalone files. Three of them show that the showcase functions are rejected once their sizes are removed. The fourth reproduces a soundness bug in the checker. |

## Parts

| Part | Contents | Needs sizes? |
|------|----------|--------------|
| `01_prelude` | `Bool`, `Nat`, `SNat`, `Maybe`, `Prod`, `Sigma`, `Eq` with `sym`/`trans`/`cong`/`subst`. Lemmas: `plus_zero`, `plus_succ`, `plus_comm`, `plus_assoc`, `append_nil`, `append_assoc`, `length_append`. Plain lists `List` and sized lists `SList` with a size-preserving `smap`. A decimal display `toDec` for readable output. | No. These are all structural. |
| `02_sized` | `sminus`, `sdiv` (floor division), `sgcd` (subtractive Euclid) on `SNat`. Quicksort via a size-preserving `partition`. Merge sort via `split`. Rose trees with `mapRose`, `flatten`, `sizeRose` (recursion through `smap`). Brouwer ordinals: `oadd`, `omul`, `collapse`. Ackermann. | **Yes** for `sdiv`, `sgcd`, `qsapp`, `msort`, `flatten`/`mapRose`/`sizeRose`. Each is rejected with "Termination check fails" once the sizes are removed (see `bad/`; `msort` was checked by hand). **Not needed** for `ack` (size-change termination finds the lexicographic order), `merge`, or the ordinals (the checker already treats `f n` as smaller than `olim f`). |
| `03_coinduction` | Sized streams: `repeat`, `iterate`, `nats`, `fibFrom`, `stmap`, `zipWith`, `interleave`, `evens`, and `umerge`, a duplicate-free merge used for a Hamming-style stream of multiples of 2 or 3. Stream processors (`ISP`/`SP`/`eat` after `examples/sp.ma`): `pairSums`, `runSum`, `adder`. A sized coinductive `Bisim` relation with cofun proofs: `bisim_refl`, `map_iterate`, `nats_iterate`, `map_succ_nats`. The inductive consequence `bisim_take`: bisimilar streams have equal prefixes. | **Yes**. Productivity of every `cofun` is checked through the size index of its result. |
| `04_compiler` | `Expr` (literals, `+`, `*`, if-zero), the denotational `evalE`, and a stack machine (`exec`/`step` with structured `ibranch`). `compile`, then **`compile_correct : exec (compile e ++ c) s ≡ exec c (evalE e :: s)`**. A constant-folding pass `cfold` with proofs `cfold_ok` and `optimised_correct`. | No. This part shows dependent types and equational proofs. The checker accepts the recursion structurally. |

### Notes on the compiler

The full theorem is proved, with if-zero included. Nothing had to be scaled
down. Three design decisions made this straightforward in Mugda:

- **Structured branches.** `ibranch then else` carries its two branches as
  nested code instead of jump offsets. With jumps, `exec` would need fuel or
  well-founded recursion, and the proof would need arithmetic on code
  addresses.
- **`exec (i :: c) s = exec c (step i s)`.** This turns the key lemma
  `exec (c1 ++ c2) s ≡ exec c2 (exec c1 s)` into a one-line induction that
  never looks at the instruction.
- **Untyped stack.** A binary operation on a stack that is too short leaves
  the stack unchanged. The theorem shows that compiled code never hits this
  case. (A depth-indexed typed stack was not needed.)

Mugda has no `with` construct. Case analysis on an intermediate value is done
with a helper function (`branch_ok`). The constant folder never uses
overlapping clauses, for the reason given under Findings: each "smart
constructor" (`foldPlus`, `foldTimes`, `foldIfz`) matches every constructor
explicitly.

### What Mugda could not express (part 3)

- **Cofuns that consume `Stream A i`.** Mugda's admissibility check rejects
  them ("type not admissible"), so stream functions take `Stream A #` inputs
  and only the result is sized. As a consequence, the self-referential classics
  are rejected:
  - `fib = 0 : zipWith (+) fib (tail fib)` fails with a type error
    (`leqSize error`), because `fib i : Stream i` is not a `Stream #`.
  - Hamming `ham = 1 : merge (map (2*) ham) (map (3*) ham)` at size `#` fails
    with "Termination check fails".

  Fibonacci is therefore generated from a state (`fibFrom x y`). The
  Hamming-style example merges two independent streams.
- A `filter` stream processor cannot be written. This is by design: the
  inductive `ISP` layer forces every processor to produce output after
  finitely many reads.

## Building and running

```sh
make showcase                 # regenerate sizedlib.ma from src/*.ma
make check-showcase           # verify that sizedlib.ma is up to date
.lake/build/bin/mugda examples/showcase/sizedlib/sizedlib.ma
```

Without `make`, run
`cat examples/showcase/sizedlib/src/*.ma > examples/showcase/sizedlib/sizedlib.ma`.

The negative examples:

```sh
for f in examples/showcase/sizedlib/bad/*.ma; do .lake/build/bin/mugda "$f"; done
```

| File | Expected result |
|------|-----------------|
| `bad/div_unsized.ma` | reject: "Termination check fails" (twice: `div` and `gcd`) |
| `bad/quicksort_unsized.ma` | reject: "Termination check fails" |
| `bad/rose_unsized.ma` | reject: "Termination check fails" |
| `bad/overlap_unsound.ma` | **accepted, but should be rejected** (soundness bug, see below) |

## Expected output

Numbers are shown in decimal via `toDec`: `(dec d1 d3)` is 13.

```
***** Mugda v1.0 (Constructive Lean 4 Edition) *****
--- scope checking ---
--- type checking ---
--- evaluating ---
digits_len evaluates to (dec d0 d8)
div_7_2 evaluates to (dec d0 d3)
div_18_7 evaluates to (dec d0 d2)
gcd_12_18 evaluates to (dec d0 d6)
ack_2_3 evaluates to (dec d0 d9)
qs_digits evaluates to (cons Dec (dec d0 d1) (cons Dec (dec d0 d1) (cons Dec (dec d0 d2) (cons Dec (dec d0 d3) (cons Dec (dec d0 d4) (cons Dec (dec d0 d5) (cons Dec (dec d0 d6) (cons Dec (dec d0 d9) (nil Dec)))))))))
ms_digits evaluates to (cons Dec (dec d0 d1) (cons Dec (dec d0 d1) (cons Dec (dec d0 d2) (cons Dec (dec d0 d3) (cons Dec (dec d0 d4) (cons Dec (dec d0 d5) (cons Dec (dec d0 d6) (cons Dec (dec d0 d9) (nil Dec)))))))))
tree_flat evaluates to (cons Dec (dec d0 d1) (cons Dec (dec d0 d2) (cons Dec (dec d0 d3) (cons Dec (dec d0 d4) (cons Dec (dec d0 d5) (cons Dec (dec d0 d6) (nil Dec)))))))
tree_size evaluates to (dec d0 d6)
tree_doubled evaluates to (cons Dec (dec d0 d2) (cons Dec (dec d0 d4) (cons Dec (dec d0 d6) (cons Dec (dec d0 d8) (cons Dec (dec d1 d0) (cons Dec (dec d1 d2) (nil Dec)))))))
collapse_w_plus_w_3 evaluates to (dec d0 d6)
collapse_w_times_3_2 evaluates to (dec d0 d6)
collapse_3_times_w_2 evaluates to (dec d0 d6)
fib_first8 evaluates to (cons Dec (dec d0 d0) (cons Dec (dec d0 d1) (cons Dec (dec d0 d1) (cons Dec (dec d0 d2) (cons Dec (dec d0 d3) (cons Dec (dec d0 d5) (cons Dec (dec d0 d8) (cons Dec (dec d1 d3) (nil Dec)))))))))
fib_8 evaluates to (dec d2 d1)
mult23_first8 evaluates to (cons Dec (dec d0 d2) (cons Dec (dec d0 d3) (cons Dec (dec d0 d4) (cons Dec (dec d0 d6) (cons Dec (dec d0 d8) (cons Dec (dec d0 d9) (cons Dec (dec d1 d0) (cons Dec (dec d1 d2) (nil Dec)))))))))
fib_plus_nats evaluates to (cons Dec (dec d0 d0) (cons Dec (dec d0 d2) (cons Dec (dec d0 d3) (cons Dec (dec d0 d5) (cons Dec (dec d0 d7) (nil Dec))))))
interleaved evaluates to (cons Dec (dec d0 d0) (cons Dec (dec d0 d1) (cons Dec (dec d0 d0) (cons Dec (dec d0 d1) (cons Dec (dec d0 d0) (cons Dec (dec d0 d1) (nil Dec)))))))
evens_nats evaluates to (cons Dec (dec d0 d0) (cons Dec (dec d0 d2) (cons Dec (dec d0 d4) (cons Dec (dec d0 d6) (cons Dec (dec d0 d8) (nil Dec))))))
sp_pairsums evaluates to (cons Dec (dec d0 d1) (cons Dec (dec d0 d5) (cons Dec (dec d0 d9) (cons Dec (dec d1 d3) (nil Dec)))))
sp_runsum evaluates to (cons Dec (dec d0 d1) (cons Dec (dec d0 d3) (cons Dec (dec d0 d6) (cons Dec (dec d1 d0) (cons Dec (dec d1 d5) (nil Dec))))))
sp_adder evaluates to (cons Dec (dec d0 d4) (cons Dec (dec d0 d4) (cons Dec (dec d0 d4) (nil Dec))))
prefix_eq evaluates to (refl (List Nat) (cons Nat zero (cons Nat (succ zero) (cons Nat (succ (succ zero)) (nil Nat)))))
prog_value evaluates to (dec d2 d0)
prog_code evaluates to (cons Instr (ipush (succ (succ zero))) (cons Instr (ipush (succ (succ (succ zero)))) (cons Instr iadd (cons Instr (ipush (succ zero)) (cons Instr (ipush zero) (cons Instr imul (cons Instr (ibranch (cons Instr (ipush (succ (succ (succ (succ zero))))) (nil Instr)) (cons Instr (ipush (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))) (nil Instr))) (cons Instr imul (nil Instr)))))))))
prog_run evaluates to (cons Dec (dec d2 d0) (nil Dec))
prog_folded evaluates to (lit (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))))))))))))))
prog_opt_code evaluates to (cons Instr (ipush (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))))))))))))))) (nil Instr))
prog_ok evaluates to (refl (List Nat) (cons Nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))))))))))))) (nil Nat)))
prog_opt_ok evaluates to (refl (List Nat) (cons Nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))))))))))))) (nil Nat)))
```

How to read some of these results:

- `qs_digits` and `ms_digits` sort `[3,1,4,1,5,9,2,6]`.
- `collapse (ω+ω) 3 = 6`, `collapse (ω·3) 2 = 6` and `collapse (3·ω) 2 = 6`.
  `collapse` follows the n-th branch at every limit.
- `sp_pairsums` runs the processor on `0,1,2,…` and gives `1,5,9,13`.
- `prog` is `(2+3) * (ifz (1*0) then 4 else 9) = 20`. Constant folding reduces
  it to a single `ipush 20`.

## Findings about the checker

These were found while writing this program. The checker was not changed.

1. **Overlapping clauses with neutral terms (Bug 6, now fixed in `Mugda/Core.lean`)**
   (`bad/overlap_unsound.ma`, `examples/counterexamples/overlap_bug.ma`). In
   original 2008 Mugda (`Value.hs`), `match` returned a 2-valued `Maybe Env`,
   treating a constructor pattern against a neutral variable as a failed match
   (`Nothing`) rather than a stuck match. A later catch-all clause (`isz x = ff`)
   then fired during conversion, reducing `isz n` to `ff` for a variable `n`
   even though `isz zero = tt`. With 3-valued `MatchResult` (`matched` |
   `mismatch` | `stuck`), `matchClauses` blocks on `stuck` and rejects
   `bad/overlap_unsound.ma` with `eqVal error`.
2. **The fuel limit is per recursion depth.** It is fixed at `defaultFuel =
   1000`. Unary numbers above roughly 60–90, or lists longer than roughly 60–90
   elements, run out of fuel when they are built inside other computations.
   For example, `nth 11 fibs` (89) fails, `nth 10 fibs` (55) works,
   `take 60 (repeat 0)` works, and `take 100 (repeat 0)` fails. SizedLib keeps
   all evaluated values small.
3. **Closed arguments are evaluated during type checking.** When an
   application `f a` is type checked, the argument `a` is evaluated, even if
   `f` has a non-dependent type. A large closed computation in an argument
   position can therefore make *type checking* fail with "out of fuel", which
   is a hard error with exit code 1. Example: `let u : Unit = ignore (nth 12
   fibs)`.
4. **An `eval` error does not change the exit code.** If the evaluation of an
   `eval let` runs out of fuel, the checker prints `eval error in …: out of
   fuel` but still exits 0.
5. **Unsized Brouwer-ordinal recursion is accepted.** `oadd x (olim f) = olim
   (\n -> oadd x (f n))` passes without sizes. The size-change order treats
   `f n` as smaller than `olim f`, which is sound for strictly positive types.
   The thesis needed an extra axiom for this.
