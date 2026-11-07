# Showcase 2: Coinductive Stream Bisimulation & Stream Fusion (`bisim.ma`)

[**← Back to Main README**](../../../README.md) | [**Showcase 1: SizedLib + Verified Compiler**](../sizedlib/README.md) | [**Tutorial**](../../../tutorial/README.md)

---

## Overview

In intentional dependent type theory, propositional equality (`Eq A x y` with constructor `refl`) cannot directly construct infinite equality proofs over coinductive streams (`Stream A #`). Instead, observational equivalence of infinite streams is expressed as **coinductive bisimulation** ($\approx$).

[`bisim.ma`](bisim.ma) develops a complete, machine-checked library of **sized coinductive stream bisimulations** in Mugda, demonstrating how **contravariant size subtyping (`-Size`)** and **size-change termination** certify coinductive equivalence proofs and stream-fusion optimizations without syntactic guardedness heuristics.

Run the showcase with:

```bash
./.lake/build/bin/mugda examples/showcase/bisim/bisim.ma
```

---

## Architecture & Verified Theorems in [`bisim.ma`](bisim.ma)

### 1. Sized Coinductive Bisimulation (`Bisim`)

```mugda
sized codata Bisim (+ A : Set) : Size -> Stream A # -> Stream A # -> Set
{
  bisimCons : (i : Size) -> (x : A) -> (xs : Stream A #) -> (ys : Stream A #) ->
              Bisim A i xs ys ->
              Bisim A ($ i) (scons A # x xs) (scons A # x ys)
}
```

- `Bisim A i s1 s2` states that the infinite streams `s1, s2 : Stream A #` agree to observation depth at least `i`.
- At limit size `#`, `Bisim A # s1 s2` is full coinductive bisimilarity ($s_1 \approx s_2$).
- Because `Bisim` is a `sized codata` family, a `cofun` proof of `(i : Size) -> Bisim A i s1 s2` is certified productive whenever matching `($ i)` on the LHS emits at least one `bisimCons` constructor before making corecursive calls at size `i < $ i`.

### 2. Equivalence Relation (`cofun`)

| Proof | Type | Description |
|-------|------|-------------|
| `bisimRefl` | `(A : Set) -> (s : Stream A #) -> (i : Size) -> Bisim A i s s` | Reflexivity ($s \approx s$) |
| `bisimSymm` | `(A : Set) -> (s1 s2 : Stream A #) -> Bisim A # s1 s2 -> (i : Size) -> Bisim A i s2 s1` | Symmetry ($s_1 \approx s_2 \implies s_2 \approx s_1$) |
| `bisimTrans` | `(A : Set) -> (s1 s2 s3 : Stream A #) -> Bisim A # s1 s2 -> Bisim A # s2 s3 -> (i : Size) -> Bisim A i s1 s3` | Transitivity ($s_1 \approx s_2 \land s_2 \approx s_3 \implies s_1 \approx s_3$) |

### 3. Stream Functor, Fusion & Interleaving Laws (`cofun`)

| Theorem | Statement |
|---------|-----------|
| `bisimMapCong` | $s_1 \approx s_2 \implies \mathsf{map}\ f\ s_1 \approx \mathsf{map}\ f\ s_2$ |
| `bisimMapId` | $\mathsf{map}\ (\lambda x.\,x)\ s \approx s$ |
| `bisimMapFusion` | $\mathsf{map}\ g\ (\mathsf{map}\ f\ s) \approx \mathsf{map}\ (\lambda x.\,g(f(x)))\ s$ |
| `bisimMapRepeat` | $\mathsf{map}\ f\ (\mathsf{repeat}\ a) \approx \mathsf{repeat}\ (f\ a)$ |
| `bisimIterateMap` | $\mathsf{iterate}\ f\ (f\ a) \approx \mathsf{map}\ f\ (\mathsf{iterate}\ f\ a)$ |
| `bisimInterleaveEvensOdds` | $\mathsf{interleave}\ (\mathsf{evens}\ s)\ (\mathsf{odds}\ s) \approx s$ *(emits 2 `bisimCons` steps per `($ ($ i))`)* |

### 4. Bridge from Coinductive `Bisim` to Inductive `Eq` (`fun`)

To extract finite propositional equalities (`Eq`) from an infinite bisimulation proof `Bisim A # s1 s2`, `bisim.ma` proves by structural induction on `n : Nat`:

- **`bisimNthEq`:** `(A : Set) -> (n : Nat) -> (s1 s2 : Stream A #) -> Bisim A # s1 s2 -> Eq A (nth A n s1) (nth A n s2)`
- **`bisimTakeEq`:** `(A : Set) -> (n : Nat) -> (s1 s2 : Stream A #) -> Bisim A # s1 s2 -> Eq (List A) (take A n s1) (take A n s2)`

Evaluating `bisimTakeEq` on `fusionWitness` and `interleaveWitness` at `n = 4` normalizes to `refl (List Nat) [1, 3, 5, 7]` and `refl (List Nat) [0, 1, 2, 3]`.

### 5. Negative Companion (`bad/bisim_unproductive.ma`)

- [`bad/bisim_unproductive.ma`](bad/bisim_unproductive.ma) shows that attempting to prove two arbitrary streams bisimilar by circular corecursion (`badBisim A s1 s2 ($ i) = badBisim A s1 s2 i` without `bisimCons`) is rejected by Mugda's contravariant subtyping check (`Bisim A i s1 s2` is not a subtype of `Bisim A ($ i) s1 s2`).
