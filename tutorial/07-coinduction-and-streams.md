# Chapter 7: Coinduction & Infinite Streams (`sized codata`)

[**← Chapter 6: Higher-Order & Nested Data**](./06-higher-order-and-nested-data.md) | [**Table of Contents**](./README.md) | [**Chapter 8: Mixing Induction & Coinduction →**](./08-mixing-induction-and-coinduction.md)

---

## 1. Duality: Termination vs. Productivity

Every data type we have written so far was introduced with `data` or `sized data`:
- An **inductive** type (`sized data`) is the **least fixed point** of its constructor functor.
- Its size index `i` is an **upper bound on tree height**: `SNat i <= SNat ($ i) <= SNat #` (**covariant**).
- Functions **consuming** an inductive type must **terminate**.

What about infinite objects — infinite streams of numbers, clocks, or communication traces?
- A **coinductive** type (`sized codata`) is the **greatest fixed point** of its constructor functor.
- Its size index `i` is a **lower bound on observation depth**: how many steps the stream is guaranteed to unfold without getting stuck.
- Therefore, subtyping runs in the **opposite (contravariant) direction**:
  $$\text{Stream } A\ \# \;\le\; \text{Stream } A\ (\$ i) \;\le\; \text{Stream } A\ i$$
  A fully defined infinite stream (`Stream A #`) can be used at any depth `i`, and a stream defined to depth `i + 1` (`Stream A ($ i)`) is also defined to depth `i` (`Stream A i`)!
- Corecursive functions (`cofun`) **producing** a coinductive type must be **productive**: to build a stream of depth `($ i)`, every corecursive call must only be needed at depth `i` (`i < $ i`).

In Mugda, inductive termination and coinductive productivity use **the exact same size-change termination checker**!

---

## 2. Walkthrough: `examples/tutorial/07_streams.ma`

Open [`examples/tutorial/07_streams.ma`](../../examples/tutorial/07_streams.ma) and run:

```bash
./.lake/build/bin/mugda examples/tutorial/07_streams.ma
```

### 2.1 Defining `Stream` and Its Destructors (`head`, `tail`, `take`, `nth`)

```mugda
sized codata Stream (+ A : Set) : Size -> Set
{
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

fun head : (A : Set) -> Stream A # -> A
{
  head .A (scons A .# x xs) = x
}

fun tail : (A : Set) -> Stream A # -> Stream A #
{
  tail .A (scons A .# x xs) = xs
}

fun take : (A : Set) -> Nat -> Stream A # -> List A
{
  take A zero     s = nil A;
  take A (succ n) s = cons A (head A s) (take A n (tail A s))
}
```

Look at `scons`:
- Given a head element `A` and a tail stream `Stream A i` defined to depth `i`, `scons A i x xs` builds a stream `Stream A ($ i)` defined to depth `i + 1`.
- At limit size `#`, since `$ # = #`, a fully defined stream `Stream A #` unpacks into a head `x : A` and a tail `xs : Stream A #`.
- Thus `head` and `tail` are ordinary `fun` definitions on `Stream A #`, and `take` extracts a finite `List A` prefix by structural recursion on `Nat`.

### 2.2 Productive Corecursive Functions (`cofun`)

To define an infinite stream, we use `cofun` and match on the target size argument using the successor size pattern `($ i)`:

```mugda
cofun repeat : (A : Set) -> A -> (i : Size) -> Stream A i
{
  repeat A a ($ i) = scons A i a (repeat A a i)
}

cofun from : Nat -> (i : Size) -> Stream Nat i
{
  from n ($ i) = scons Nat i n (from (succ n) i)
}
```

Why does `repeat` pass Mugda's checks?
1. **Admissibility (`admissible`):** Matching on `($ i)` is allowed in a `cofun` because `i` occurs negatively (contravariantly) in the target type `Stream A i`.
2. **Typing:** On the LHS, `($ i)` refines the expected return type to `Stream A ($ i)`. On the RHS, `scons A i a (...)` produces `Stream A ($ i)` provided the tail has type `Stream A i`.
3. **Productivity via SCT:** The corecursive call `repeat A a i` is at size `i < $ i`!
4. **Instantiating at `#`:** Once `repeat` is checked for all `i : Size`, `repeat A a # : Stream A #` is a fully defined infinite stream!

### 2.3 Stream Transformers (`map`, `zipWith`), Fibonacci, Multi-Step & Mutual Corecursion

In [`07_streams.ma`](../../examples/tutorial/07_streams.ma), you will also see four common corecursive patterns:

1. **Stream transformers (`map`, `zipWith`):**
   ```mugda
   cofun map : (A : Set) -> (B : Set) -> (A -> B) -> Stream A # -> (i : Size) -> Stream B i
   {
     map .A B f (scons A .# x xs) ($ i) = scons B i (f x) (map A B f xs i)
   }
   ```
2. **Fibonacci with accumulators (`fibFrom`):**
   ```mugda
   cofun fibFrom : Nat -> Nat -> (i : Size) -> Stream Nat i
   {
     fibFrom x y ($ i) = scons Nat i x (fibFrom y (add x y) i)
   }
   ```
3. **Emitting two elements per step (`twoAtATime`):**
   ```mugda
   cofun twoAtATime : Nat -> (i : Size) -> Stream Nat i
   {
     twoAtATime n ($ ($ i)) = scons Nat ($ i) n (scons Nat i n (twoAtATime (succ n) i))
   }
   ```
   Matching `($ ($ i))` on the LHS asks for depth `i + 2`; emitting two `scons` constructors reduces the required tail depth to `i < $ ($ i)`!
4. **Mutual corecursion (`ticks` and `tocks`):**
   ```mugda
   mutual
   {
     cofun ticks : (i : Size) -> Stream Bool i
     { ticks ($ i) = scons Bool i tt (tocks i) }

     cofun tocks : (i : Size) -> Stream Bool i
     { tocks ($ i) = scons Bool i ff (ticks i) }
   }
   ```
5. **Coinductive subtyping (`anySize`, `shallow`):**
   ```mugda
   let anySize : (A : Set) -> (i : Size) -> Stream A # -> Stream A i = \ A -> \ i -> \ s -> s
   let shallow : (A : Set) -> (i : Size) -> Stream A ($ i) -> Stream A i = \ A -> \ i -> \ s -> s
   ```

---

## 3. Four Classic Coinduction Pitfalls (Negative Examples)

Each of the following four negative files in `examples/tutorial/` demonstrates an unproductive or ill-typed stream definition that Mugda rejects:

| File | What It Attempts | Why Mugda Rejects It |
|------|------------------|----------------------|
| [`07_unproductive_bad.ma`](../../examples/tutorial/07_unproductive_bad.ma) | `cofun bad : (i : Size) -> Stream i { bad ($ i) = bad ($ i) }` (no `scons` constructor emitted) | `termination check fails for [bad]` (`$ i` does not decrease) |
| [`07_unproductive_type_bad.ma`](../../examples/tutorial/07_unproductive_type_bad.ma) | `cofun bad : (i : Size) -> Stream i { bad ($ i) = bad i }` (decreases `i`, but forgets `scons`) | Type error (`leqVal`): `bad i` has type `Stream i`, which is **not** a subtype of `Stream ($ i)`! |
| [`07_filter_bad.ma`](../../examples/tutorial/07_filter_bad.ma) | Stream `filter` that drops elements when `p x = ff` without emitting `scons` | Rejected! Either the recursive call keeps size `($ i)` (failing SCT) or drops to `i` (failing `Stream i <= Stream ($ i)`) |
| [`07_tail_bad.ma`](../../examples/tutorial/07_tail_bad.ma) | Defining `tail` at size `i` (`Stream i -> Stream i`) and using `scons i z (tail ($ i) (bad i))` | Type error (`leqVal`): `tail ($ i)` requires `Stream ($ ($ i))`, which `bad i : Stream i` cannot provide |

Look closely at the pair `07_unproductive_bad.ma` and `07_unproductive_type_bad.ma` — together they show how **contravariant subtyping** and **size-change termination** work hand in hand:
- If you don't emit a constructor and call `bad ($ i)` at the same size, **SCT** catches you.
- If you don't emit a constructor and call `bad i` at the smaller size `i`, **contravariant subtyping (`Stream i <= Stream ($ i)` fails!)** catches you!
- The *only* way to turn a `Stream i` into a `Stream ($ i)` is to wrap it in `scons i x (...)` — which is the semantic counterpart of constructor guardedness!

---

## 4. Exercises

1. **Stream Interleaving (`interleave`) and `evens`/`odds`:**
   - Write `interleave : (A : Set) -> (i : Size) -> Stream A # -> Stream A # -> Stream A i` that alternates elements from two streams.
   - Write `evens` and `odds` that take every even-indexed / odd-indexed element of a `Stream A #`.
   - Compare your solution with [`examples/tutorial/solutions/sol_07_stream_interleave.ma`](../../examples/tutorial/solutions/sol_07_stream_interleave.ma).

---

[**← Chapter 6: Higher-Order & Nested Data**](./06-higher-order-and-nested-data.md) | [**Table of Contents**](./README.md) | [**Chapter 8: Mixing Induction & Coinduction →**](./08-mixing-induction-and-coinduction.md)
