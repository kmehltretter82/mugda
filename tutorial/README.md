# Sized Types with Mugda — A Hands-On Tutorial

Welcome to **Sized Types with Mugda**, a practical, example-driven guide to dependently typed programming, size-change termination (SCT), and sized inductive/coinductive types in Karl Mehltretter's **Mugda** language (Constructive Lean 4 Edition).

Every code example in this tutorial lives in [`examples/tutorial/`](../examples/tutorial/) (with exercise solutions in [`examples/tutorial/solutions/`](../examples/tutorial/solutions/)) and is automatically verified on every commit by [`tests/golden.sh`](../tests/golden.sh) and [`tests/js-vs-lean.mjs`](../tests/js-vs-lean.mjs).

---

## Quick Start

### 1. Run via the Native Lean 4 CLI

```bash
# Build the Lean 4 checker and proofs:
lake build

# Run any tutorial file:
.lake/build/bin/mugda examples/tutorial/01_first_steps.ma
.lake/build/bin/mugda examples/tutorial/03_sized_nat.ma
.lake/build/bin/mugda examples/tutorial/07_streams.ma
```

### 2. Try in the Browser Playground

Open the [**Live Mugda Web Playground**](https://kmehltretter82.github.io/mugda/) to edit and run Mugda programs in your browser, inspect call matrices, and compare **Bug-Fixed Mugda** against **Original 2008 Mugda**.

---

## Chapters

| Chapter | Topic | Positive Examples | Negative Counterexamples (Rejected) |
| :--- | :--- | :--- | :--- |
| [**Chapter 1**](01-first-steps.md) | **First Steps: Explicit Dependent Types** | [`01_first_steps.ma`](../examples/tutorial/01_first_steps.ma) | [`01_first_steps_bad.ma`](../examples/tutorial/01_first_steps_bad.ma) |
| [**Chapter 2**](02-termination-without-sizes.md) | **Termination Without Sizes: Size-Change Matrices (`ORDER_+`)** | [`02_termination.ma`](../examples/tutorial/02_termination.ma) | [`02_div_bad.ma`](../examples/tutorial/02_div_bad.ma), [`02_gcd_bad.ma`](../examples/tutorial/02_gcd_bad.ma), [`02_quicksort_bad.ma`](../examples/tutorial/02_quicksort_bad.ma), [`02_loop_bad.ma`](../examples/tutorial/02_loop_bad.ma) |
| [**Chapter 3**](03-sized-inductive-types.md) | **Sized Inductive Types: `Size`, `$ i`, `#`, and Euclidean Division/GCD** | [`03_sized_nat.ma`](../examples/tutorial/03_sized_nat.ma) | [`03_div_bad.ma`](../examples/tutorial/03_div_bad.ma) |
| [**Chapter 4**](04-sized-lists-and-sorting.md) | **Sized Lists, Quicksort & Mergesort** | [`04_sized_lists.ma`](../examples/tutorial/04_sized_lists.ma) | [`04_quicksort_bad.ma`](../examples/tutorial/04_quicksort_bad.ma) |
| [**Chapter 5**](05-subtyping-and-variance.md) | **Subtyping, Variance (`+` Parameters) & Strict Positivity** | [`05_subtyping.ma`](../examples/tutorial/05_subtyping.ma) | [`05_down_bad.ma`](../examples/tutorial/05_down_bad.ma), [`05_invariant_bad.ma`](../examples/tutorial/05_invariant_bad.ma), [`05_negative_bad.ma`](../examples/tutorial/05_negative_bad.ma), [`05_param_bad.ma`](../examples/tutorial/05_param_bad.ma), [`05_rose_bad.ma`](../examples/tutorial/05_rose_bad.ma) |
| [**Chapter 6**](06-higher-order-and-nested-data.md) | **Higher-Order & Nested Data: Brouwer Ordinals, Rose Trees & `addWith`** | [`06_higher_order.ma`](../examples/tutorial/06_higher_order.ma) | [`06_rose_bad.ma`](../examples/tutorial/06_rose_bad.ma), [`06_addwith_bad.ma`](../examples/tutorial/06_addwith_bad.ma) |
| [**Chapter 7**](07-coinduction-and-streams.md) | **Coinduction: `sized codata`, `cofun`, Productivity & Streams** | [`07_streams.ma`](../examples/tutorial/07_streams.ma) | [`07_unproductive_bad.ma`](../examples/tutorial/07_unproductive_bad.ma), [`07_unproductive_type_bad.ma`](../examples/tutorial/07_unproductive_type_bad.ma), [`07_filter_bad.ma`](../examples/tutorial/07_filter_bad.ma), [`07_tail_bad.ma`](../examples/tutorial/07_tail_bad.ma) |
| [**Chapter 8**](08-mixing-induction-and-coinduction.md) | **Mixing Induction & Coinduction: Stream Processors (`ISP` inside `SP`)** | [`08_stream_processors.ma`](../examples/tutorial/08_stream_processors.ma) | [`08_getforever_bad.ma`](../examples/tutorial/08_getforever_bad.ma), [`08_coget_bad.ma`](../examples/tutorial/08_coget_bad.ma) |
| [**Chapter 9**](09-pitfalls-and-soundness.md) | **Pitfalls, Soundness Rules & Machine-Checked Lean 4 Metatheorems** | [`09_soundness_ok.ma`](../examples/tutorial/09_soundness_ok.ma) | [`09_incomplete_size_bad.ma`](../examples/tutorial/09_incomplete_size_bad.ma), [`09_inadmissible_bad.ma`](../examples/tutorial/09_inadmissible_bad.ma), [`09_deep_limit_bad.ma`](../examples/tutorial/09_deep_limit_bad.ma), [`09_overlap_bad.ma`](../examples/tutorial/09_overlap_bad.ma) |

---

## Exercise Solutions

- [**Chapter 1 Solutions**](../examples/tutorial/solutions/sol_01_bool_nat.ma): `xor`, `mul`, `exp`
- [**Chapter 2 Solutions**](../examples/tutorial/solutions/sol_02_sct_lex.ma): mutual `isEven`/`isOdd`, `half`, lexicographic `lexCount`
- [**Chapter 3 Solutions**](../examples/tutorial/solutions/sol_03_snat_mod.ma): size-preserving `minus` and Euclidean `modAux` on `SNat`
- [**Chapter 4 Solutions**](../examples/tutorial/solutions/sol_04_slist_dedup.ma): size-preserving `sfilter` on `SList`
- [**Chapter 7 Solutions**](../examples/tutorial/solutions/sol_07_stream_interleave.ma): productive `interleave` and `evens` on `Stream`

---

## Next Step After the Tutorial: The Showcase Project

Once you have worked through the tutorial, explore [**SizedLib + Verified Expression Compiler**](../examples/showcase/sizedlib/README.md) ([`examples/showcase/sizedlib/sizedlib.ma`](../examples/showcase/sizedlib/sizedlib.ma)), an ~1,100-line multi-part Mugda development combining sized arithmetic, sorting, rose trees, Brouwer ordinals, coinductive streams, stream processors, and a machine-checked compiler with constant-folding optimization.
