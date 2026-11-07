# Chapter 4 — Sized Lists, Quicksort & Mergesort

**Companion files:**
- Accepted: [`examples/tutorial/04_sized_lists.ma`](../examples/tutorial/04_sized_lists.ma)
- Rejected: [`examples/tutorial/04_quicksort_bad.ma`](../examples/tutorial/04_quicksort_bad.ma)
- Solutions: [`examples/tutorial/solutions/sol_04_slist_dedup.ma`](../examples/tutorial/solutions/sol_04_slist_dedup.ma)

---

## 1. Sized Lists (`SList`)

From [`04_sized_lists.ma`](../examples/tutorial/04_sized_lists.ma):

```mugda
sized data SList (+ A : Set) : Size -> Set {
  nil  : (i : Size) -> SList A ($ i) ;
  cons : (i : Size) -> A -> SList A i -> SList A ($ i)
}
```

Notice two features:
1. The element type `+ A : Set` is marked strictly positive (`+`), making `SList A i` covariant in `A` as well as in `i`.
2. Just as `minus` preserved the size bound `i` on `SNat i`, list transformations that never lengthen a list (`map`, `filter`, `partition`, `split`) preserve `i` in their return type!

---

## 2. Size-Preserving `filter` and `partition`

In `filter`:

```mugda
fun filter : (A : Set) -> (A -> Bool) -> (i : Size) -> SList A i -> SList A i {
  filter A p .($ i) (nil .A i)       = nil A i ;
  filter A p .($ i) (cons .A i x xs) =
    ite (SList A ($ i)) (p x)
      (cons A i x (filter A p i xs))
      (filter A p i xs)
}
```

Look closely at the `ite` branches:
- When `p x` is `tt`, `cons A i x (filter A p i xs)` has type `SList A ($ i)`.
- When `p x` is `ff`, `filter A p i xs` has type `SList A i`, which is automatically coerced to `SList A ($ i)` by size subtyping (`SList A i <= SList A ($ i)`)!

Similarly, `partition` splits an `SList A i` into a pair `Prod (SList A i)` of two lists, **both bounded by the same size `i`**:

```mugda
fun partition : (A : Set) -> (A -> Bool) -> (i : Size) -> SList A i -> Prod (SList A i)
```

---

## 3. Quicksort and Mergesort

Because `partition A (leq x) i xs` returns a `Prod (SList A i)` when `cons .A i x xs : SList A ($ i)`, both halves `fst ...` and `snd ...` have type `SList A i`:

```mugda
fun qsort : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i -> SList A # {
  qsort A leq .($ i) (nil .A i)       = nil A # ;
  qsort A leq .($ i) (cons .A i x xs) =
    let p : Prod (SList A i) = partition A (\ y -> leq y x) i xs in
    append A # (qsort A leq i (fst (SList A i) p))
      (cons A # x (qsort A leq i (snd (SList A i) p)))
}
```

Both recursive calls `qsort A leq i ...` are at size `i < $ i`! The exact same pattern makes `split` and `msort` (mergesort) pass in [`04_sized_lists.ma`](../examples/tutorial/04_sized_lists.ma).

---

## 4. Exercises

1. Write a standalone `sfilter` that removes all `zero` elements from an `SList Nat #` and test it with `eval let`.

Compare your solution with [`examples/tutorial/solutions/sol_04_slist_dedup.ma`](../examples/tutorial/solutions/sol_04_slist_dedup.ma).
