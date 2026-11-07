# Chapter 6: Higher-Order Recursion & Nested Data (Ordinals & Rose Trees)

[**← Chapter 5: Subtyping & Variance**](./05-subtyping-and-variance.md) | [**Table of Contents**](./README.md) | [**Chapter 7: Coinduction & Streams →**](./07-coinduction-and-streams.md)

---

## 1. Where Syntactic Guardedness Breaks Down

In Chapter 3 we saw how sized types certify non-structural recursion on flat numbers and lists (`minus`, `div`, `merge`, `quicksort`). A second major place where syntactic guardedness fails is **higher-order and nested inductive data**:
1. **Infinitely branching trees (Brouwer ordinals `SOrd`)**, where a constructor stores a *function* `Nat -> SOrd i`;
2. **Nested data (Rose trees `Tree`)**, where a constructor stores a list of child subtrees `SList (Tree A i) #`, and recursive functions (`mapT`, `flat`) pass themselves **partially applied** to `mapL`;
3. **Higher-order recursion combinators (`addWith`)**, which take an arbitrary size-preserving function `f : (k : Size) -> SNat k -> SNat k` as a parameter and swap arguments on recursive calls.

---

## 2. Walkthrough: `examples/tutorial/06_higher_order.ma`

Open [`examples/tutorial/06_higher_order.ma`](../../examples/tutorial/06_higher_order.ma) and run:

```bash
./.lake/build/bin/mugda examples/tutorial/06_higher_order.ma
```

### 2.1 Infinitely Branching Brouwer Ordinals (`SOrd`)

```mugda
sized data SOrd : Size -> Set
{
  ozero : (i : Size) -> SOrd ($ i);
  olim  : (i : Size) -> (Nat -> SOrd i) -> SOrd ($ i)
}

fun addOrd : SOrd # -> (i : Size) -> SOrd i -> SOrd #
{
  addOrd x .($ i) (ozero i)  = x;
  addOrd x .($ i) (olim i f) = olim # (\ n -> addOrd x i (f n))
}
```

Look at `olim`: its second argument is a function `f : Nat -> SOrd i` producing countably many subtrees, each of size `i`.
- Because `Nat` does not mention `SOrd` and the codomain `SOrd i` is strictly positive in `SOrd`, `olim` passes the strict positivity check (`sposConstructor`).
- In `addOrd`, applying `f n` yields an ordinal of size `i < $ i`, so the recursive call `addOrd x i (f n)` terminates by the size-change check on `i`.

### 2.2 Rose Trees (`Tree`) and Higher-Order `mapL`

Now look at how `Tree` nests inside `SList`:

```mugda
sized data SList (+ A : Set) : Size -> Set
{
  nil  : (i : Size) -> SList A ($ i);
  cons : (i : Size) -> A -> SList A i -> SList A ($ i)
}

sized data Tree (+ A : Set) : Size -> Set
{
  leaf : (i : Size) -> A -> Tree A ($ i);
  node : (i : Size) -> SList (Tree A i) # -> Tree A ($ i)
}
```

Notice two crucial details in `node : (i : Size) -> SList (Tree A i) # -> Tree A ($ i)`:
1. `SList` must declare its element parameter `(+ A : Set)` as **covariant (`+`)**! Otherwise `Tree` would fail strict positivity and size covariance (`examples/tutorial/06_rose_bad.ma`).
2. A `Tree A ($ i)` of height at most `i + 1` contains a list of arbitrary length `#` (`SList ... #`), whose elements are subtrees `Tree A i` of height at most `i`.

Now look at `mapT` and `flat`:

```mugda
fun mapT : (A : Set) -> (B : Set) -> (A -> B) -> (i : Size) -> Tree A i -> Tree B i
{
  mapT .A B f .($ i) (leaf A i a)  = leaf B i (f a);
  mapT .A B f .($ i) (node A i ts) =
    node B i (mapL (Tree A i) (Tree B i) (mapT A B f i) # ts)
}

fun flat : (A : Set) -> (i : Size) -> Tree A i -> SList A #
{
  flat .A .($ i) (leaf A i a)  = cons A # a (nil A #);
  flat .A .($ i) (node A i ts) =
    concat A # (mapL (Tree A i) (SList A #) (flat A i) # ts)
}
```

Why do `mapT` and `flat` pass the termination checker without needing a mutually recursive `mapTList` or `flatList`?
- In `mapT`, the recursive call `mapT A B f i` is **partially applied** (it is not applied to any tree argument at the call site; it is passed as a function of type `Tree A i -> Tree B i` to `mapL`).
- Mugda's termination checker does not need to inspect the body of `mapL`! The 4th argument of `mapT` on the LHS is `.($ i)` and on the RHS is `i`, so the partial application `mapT A B f i` already exhibits a strict decrease `i < $ i`!

### 2.3 Higher-Order Size-Preserving Functions + Permuted Sizes (`addWith`)

Finally, look at lines 109–137 of [`06_higher_order.ma`](../../examples/tutorial/06_higher_order.ma) (from thesis §5.4.4):

```mugda
-- "one-two-eliminate": size preserving, so it fits the argument type of addWith
fun ote : (i : Size) -> SNat i -> SNat i
{
  ote .($ i)     (szero i)                  = szero i;
  ote .($ ($ i)) (ssucc .($ i) (szero i))   = szero i;
  ote .($ ($ i)) (ssucc .($ i) (ssucc i x)) = ssucc ($ i) (ssucc i (ote i x))
}

fun addWith : ((k : Size) -> SNat k -> SNat k) ->
              (i : Size) -> (j : Size) -> SNat i -> SNat j -> SNat #
{
  addWith f .($ i) j (szero i)   y = y;
  addWith f .($ i) j (ssucc i x) y = ssucc # (addWith f j i (f j y) (f i x))
}
```

Look at what `addWith` does in its second clause:
- It takes an arbitrary size-preserving function `f : (k : Size) -> SNat k -> SNat k`.
- In the recursive call `addWith f j i (f j y) (f i x)`, the two size arguments `i` and `j` **swap positions**!
- Neither sized types alone (because `i` and `j` swap) nor syntactic SCT alone (because `x` and `y` are wrapped in unknown higher-order calls `f j y` and `f i x`) can prove termination of `addWith`.
- **Together**, sized types tell the checker that `f j y : SNat j` and `f i x : SNat i`, and Lee–Jones–Ben-Amram `ORDER_+` closure proves that every 2-step cycle swaps `(i, j) -> (j, i') -> (i', j')` with `i' < i` and `j' < j`!

---

## 3. What Goes Wrong Without Sizes or Polarities? (Negative Examples)

### 3.1 Missing `+` Polarity on `List` (`06_rose_bad.ma`)

In [`examples/tutorial/06_rose_bad.ma`](../../examples/tutorial/06_rose_bad.ma), `List (A : Set)` is declared with default invariant polarity instead of `(+ A : Set)`, and `Rose` tries to nest `List Rose`:

```bash
./.lake/build/bin/mugda examples/tutorial/06_rose_bad.ma
```

Output:
```text
checkData: constructor argument not strictly positive
```

Because `A` is not declared `+` in `List`, Mugda refuses to trust that `Rose` appears only in strictly positive positions inside `List Rose`.

### 3.2 Non-Size-Preserving Function Argument (`06_addwith_bad.ma`)

In [`examples/tutorial/06_addwith_bad.ma`](../../examples/tutorial/06_addwith_bad.ma), `badAddWith` takes an unsized function `f : SNat # -> SNat #` that loses the size bound `i`:

```bash
./.lake/build/bin/mugda examples/tutorial/06_addwith_bad.ma
```

Because `f x` only has type `SNat #` instead of `SNat i`, it cannot be passed where `SNat i` is required, or if sizes are fixed to `#`, the termination check fails.

---

## 4. Exercises

1. **Preorder Traversal with Node Labels:** Extend `Tree` in [`06_higher_order.ma`](../../examples/tutorial/06_higher_order.ma) so that internal `node` constructors also carry a label `a : A`, and update `mapT` and `flat` accordingly.
2. **Ordinal Multiplication (`mulOrd`):** Using `addOrd`, define ordinal multiplication `mulOrd : SOrd # -> (i : Size) -> SOrd i -> SOrd #`.

---

[**← Chapter 5: Subtyping & Variance**](./05-subtyping-and-variance.md) | [**Table of Contents**](./README.md) | [**Chapter 7: Coinduction & Streams →**](./07-coinduction-and-streams.md)
