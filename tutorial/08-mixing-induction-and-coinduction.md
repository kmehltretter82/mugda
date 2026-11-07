# Chapter 8: Mixing Induction & Coinduction (Stream Processors)

[**← Chapter 7: Coinduction & Streams**](./07-coinduction-and-streams.md) | [**Table of Contents**](./README.md) | [**Chapter 9: Pitfalls, Counterexamples & Soundness →**](./09-pitfalls-and-soundness.md)

---

## 1. Mixed Inductive/Coinductive Types

In Chapters 3–6 we studied **inductive** types (`data` / `sized data`) for finite structures, and in Chapter 7 we studied **coinductive** types (`sized codata`) for infinite structures.

Many reactive systems combine **both**:
> *A stream processor reads **finitely many** input elements (`get`) before writing (`put`) one output element, and repeats this process **forever**!*

Notice the two layers:
- **Inner layer (inductive, `data ISP`):** One round of reading inputs (`get`) until an output (`put`) is ready. Because this layer is inductive, a processor can only perform **finitely many** `get` operations before reaching `put` (preventing livelock!).
- **Outer layer (coinductive, `sized codata SP`):** Infinitely many rounds chained together, where the continuation `K` after each `put` is again a stream processor `SP i`!

This is Ghani, Hancock, and Pattinson's **Stream Processor** representation (thesis §5.5.4 and [`examples/sp.ma`](../../examples/sp.ma)).

---

## 2. Walkthrough: `examples/tutorial/08_stream_processors.ma`

Open [`examples/tutorial/08_stream_processors.ma`](../../examples/tutorial/08_stream_processors.ma) and run:

```bash
./.lake/build/bin/mugda examples/tutorial/08_stream_processors.ma
```

### 2.1 Nesting Inductive `ISP` Inside Coinductive `SP`

```mugda
-- one round: some gets, then a put with the continuation K
data ISP (+ K : Set) : Set
{
  put : Nat -> K -> ISP K;
  get : (Nat -> ISP K) -> ISP K
}

-- infinitely many rounds
sized codata SP : Size -> Set
{
  isp : (i : Size) -> ISP (SP i) -> SP ($ i)
}
```

Let's trace how `ISP` and `SP` fit together:
1. `ISP (+ K : Set)` is an **inductive** type parameterized covariantly (`+`) by a continuation type `K`.
   - `put b k` outputs a `Nat` (`b`) and hands over a continuation `k : K`.
   - `get f` reads a `Nat` from the input stream and continues the current round with `f a : ISP K`.
   - Because `ISP` is inductive (`data`), any value of `ISP K` is a well-founded tree of `get`s whose leaves are `put`s!
2. `SP : Size -> Set` is a **sized coinductive** type (`sized codata`).
   - Why was `+ K` essential in `data ISP (+ K : Set)`? Because `isp : (i : Size) -> ISP (SP i) -> SP ($ i)` nests `SP i` inside `ISP (...)`! Since `ISP` is covariant in `K`, `SP` is strictly positive in `ISP (SP i)` and contravariant in `i`!

### 2.2 Running a Stream Processor (`ieat` and `eat`)

Because Mugda does not mix `fun` and `cofun` inside a single `mutual` block, we run `ISP` and `SP` in continuation-passing style using two separate functions:
1. **`ieat` (`fun`):** Runs **one inductive round** `ISP K` by structural recursion on `ISP K`. When it reaches `put K b k`, it passes the output `b`, the continuation `k : K`, and the remaining input stream `as` to a callback `h : Nat -> K -> Stream # -> C`:
   ```mugda
   fun ieat : (K : Set) -> (C : Set) -> ISP K -> Stream # -> (Nat -> K -> Stream # -> C) -> C
   {
     ieat .K C (get K f)   (scons .# a as) h = ieat K C (f a) as h;
     ieat .K C (put K b k) as              h = h b k as
   }
   ```
   Look at `ieat`: in the `get` clause, `(f a)` is a structural subterm of `(get K f)`, so `ieat` terminates by structural recursion!

2. **`eat` (`cofun`):** Runs a processor `SP #` **forever** to produce a `Stream i`:
   ```mugda
   cofun eat : SP # -> Stream # -> (i : Size) -> Stream i
   {
     eat (isp .# ip) as ($ i) =
       ieat (SP #) (Stream ($ i)) ip as
            (\ b -> \ k -> \ as' -> scons i b (eat k as' i))
   }
   ```
   Look at how `eat` is certified productive:
   - On the LHS, `eat` matches `($ i)` to produce `Stream ($ i)`.
   - On the RHS, it calls `ieat` on `ip : ISP (SP #)` with the continuation `\ b -> \ k -> \ as' -> scons i b (eat k as' i)`.
   - Inside that continuation, `scons i b (...)` produces a `Stream ($ i)` from `eat k as' i : Stream i`, where the corecursive call `eat k as' i` is at strictly smaller size `i < $ i`!
   - Even though the corecursive call `eat k as' i` is buried inside a lambda passed to another function (`ieat`), Mugda's size-change termination checker sees `i < $ i` immediately!

### 2.3 Example Processors: `doubler`, `pairSum`, and `stutter`

In [`08_stream_processors.ma`](../../examples/tutorial/08_stream_processors.ma), we define three processors and evaluate them on `0, 1, 2, 3, ...`:

```mugda
-- 1 get per 1 put: doubles every input (0, 2, 4, 6, ...)
cofun doubler : (i : Size) -> SP i
{
  doubler ($ i) = isp i (get (SP i) (\ n -> put (SP i) (add n n) (doubler i)))
}

-- 2 gets per 1 put: sums adjacent pairs (0+1=1, 2+3=5, 4+5=9, 6+7=13, ...)
cofun pairSum : (i : Size) -> SP i
{
  pairSum ($ i) =
    isp i (get (SP i) (\ m -> get (SP i) (\ n -> put (SP i) (add m n) (pairSum i))))
}

-- 1 get per 2 puts: echoes each element twice (0, 0, 1, 1, ...)
cofun stutter : (i : Size) -> SP i
{
  stutter ($ ($ i)) =
    isp ($ i) (get (SP ($ i)) (\ n -> put (SP ($ i)) n (isp i (put (SP i) n (stutter i)))))
}
```

---

## 3. Why Livelock Is Impossible (Negative Examples)

What happens if someone tries to write a stream processor that reads inputs forever (`get`) without ever emitting a `put`?

### 3.1 Infinite `get` Loop (`08_getforever_bad.ma`)

In [`examples/tutorial/08_getforever_bad.ma`](../../examples/tutorial/08_getforever_bad.ma):

```mugda
fun getForever : (K : Set) -> ISP K
{
  getForever K = get K (\ n -> getForever K)
}
```

Run Mugda on `08_getforever_bad.ma`:

```bash
./.lake/build/bin/mugda examples/tutorial/08_getforever_bad.ma
```

Output:
```text
termination check fails for [getForever]
```

Because `ISP` is inductive (`data`), `getForever` is a `fun` with no decreasing argument, so SCT rejects it.

### 3.2 Making `get` Coinductive (`08_coget_bad.ma`)

What if someone tries to avoid `ISP` by putting both `get` and `put` directly into a single `codata SP`, and then writing `eat`?

Run Mugda on [`examples/tutorial/08_coget_bad.ma`](../../examples/tutorial/08_coget_bad.ma):

```bash
./.lake/build/bin/mugda examples/tutorial/08_coget_bad.ma
```

Output:
```text
termination check fails for [eat]
```

When `get` is coinductive, the `get` clause of `eat`:
```mugda
eat (get .# f) (scons .# a as) ($ i) = eat (f a) as ($ i)
```
cannot emit an `scons` onto the output stream, so the recursive call must still produce `Stream ($ i)` at the same size `($ i)` — and because `get` is `codata`, `(f a)` is not an inductive subterm either!

---

## 4. Exercises

1. **Skip Every Other Input (`evensSP`):** Write a `cofun evensSP : (i : Size) -> SP i` that reads two inputs `m, n`, outputs `m`, discards `n`, and repeats.
2. **Running Sum (`scanSP`):** Write a `cofun scanFrom : Nat -> (i : Size) -> SP i` that maintains an accumulator `acc : Nat`, reads an input `n`, outputs `add acc n`, and continues with `scanFrom (add acc n) i`.

---

[**← Chapter 7: Coinduction & Streams**](./07-coinduction-and-streams.md) | [**Table of Contents**](./README.md) | [**Chapter 9: Pitfalls, Counterexamples & Soundness →**](./09-pitfalls-and-soundness.md)
