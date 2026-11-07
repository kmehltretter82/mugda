# Chapter 3 — Sized Inductive Types: `Size`, `$ i`, `#`, and Euclidean Division/GCD

**Companion files:**
- Accepted: [`examples/tutorial/03_sized_nat.ma`](../examples/tutorial/03_sized_nat.ma)
- Rejected: [`examples/tutorial/03_div_bad.ma`](../examples/tutorial/03_div_bad.ma)
- Solutions: [`examples/tutorial/solutions/sol_03_snat_mod.ma`](../examples/tutorial/solutions/sol_03_snat_mod.ma)

---

## 1. The `Size` Sort, `$ i`, and `#`

Mugda adds a built-in sort `Size` representing ordinal upper bounds on constructor height (inductive types) or observation depth (coinductive types):

- **`i : Size`**: a size variable.
- **`$ i`**: the successor size ($\alpha + 1$).
- **`#`**: the top / closure ordinal ($\infty$), satisfying **`$ # = #`** ([`sinfty_infty`](../Mugda/Metatheory.lean#L32)) and **`i <= #`** for all sizes `i` ([`leqSize_infty`](../Mugda/Metatheory.lean#L40)).

In a `sized data` declaration, every constructor takes a size `i : Size` for its recursive arguments and constructs a value at the successor size `$ i`:

```mugda
sized data SNat : Size -> Set {
  zero : (i : Size) -> SNat ($ i) ;
  succ : (i : Size) -> SNat i -> SNat ($ i)
}
```

Closed values live at `SNat #`: since `$ # = #`, `zero # : SNat #` and `succ # n : SNat #`.

---

## 2. Why `minus : (i : Size) -> SNat i -> SNat # -> SNat i` Unlocks `div` and `gcd`

Look at the type of `minus` in [`03_sized_nat.ma`](../examples/tutorial/03_sized_nat.ma):

```mugda
fun minus : (i : Size) -> SNat i -> SNat # -> SNat i {
  minus .($ i) (zero i)   y           = zero i ;
  minus .($ i) (succ i x) (zero .#)   = succ i x ;
  minus .($ i) (succ i x) (succ .# y) = minus i x y
}
```

Let's trace what this type says:
1. The first number has size `i` (`SNat i`), and the second number can have **any** size (`SNat #`).
2. The result has type **`SNat i`** — its height is bounded by the height `i` of the first argument!
3. In the first two clauses, `zero i` and `succ i x` already have type `SNat ($ i)`.
4. In the third clause, `minus i x y` has type `SNat i`, which is a **subtype** of the expected return type `SNat ($ i)` because `SNat` is covariant in its size index (`i <= $ i`, proved in [`leqSize_succ_gen`](../Mugda/Metatheory.lean#L49) and [`leqApp_sized_variance`](../Mugda/Metatheory.lean#L834))!

Now look at `div` in [`03_sized_nat.ma`](../examples/tutorial/03_sized_nat.ma):

```mugda
fun div : (i : Size) -> SNat i -> SNat # -> SNat i {
  div .($ i) (zero i)   y = zero i ;
  div .($ i) (succ i x) y = succ i (div i (minus i x y) y)
}
```

Because `x : SNat i`, `minus i x y` ALSO has type `SNat i`! So `div` can make its recursive call at the **strictly smaller size `i` < `$ i`**, and the SCT checker sees the size decrease `.($ i) -> i` immediately!

> [!IMPORTANT]
> Compare [`03_div_bad.ma`](../examples/tutorial/03_div_bad.ma): if you give `minus` the weaker return type `SNat #` instead of `SNat i`, then `minus i x y` only has type `SNat #`, forcing `div` to recurse at size `#`, which fails the termination check!

---

## 3. Exercises

1. Using `minus` and `leq`, write Euclidean remainder `modAux : (i : Size) -> Bool -> SNat i -> SNat # -> SNat #` and compute `7 mod 3`.

Compare your solution with [`examples/tutorial/solutions/sol_03_snat_mod.ma`](../examples/tutorial/solutions/sol_03_snat_mod.ma).
