# Chapter 2 — Termination Without Sizes: Size-Change Matrices (`ORDER_+`)

**Companion files:**
- Accepted: [`examples/tutorial/02_termination.ma`](../examples/tutorial/02_termination.ma)
- Rejected: [`02_div_bad.ma`](../examples/tutorial/02_div_bad.ma), [`02_gcd_bad.ma`](../examples/tutorial/02_gcd_bad.ma), [`02_quicksort_bad.ma`](../examples/tutorial/02_quicksort_bad.ma), [`02_loop_bad.ma`](../examples/tutorial/02_loop_bad.ma)
- Solutions: [`examples/tutorial/solutions/sol_02_sct_lex.ma`](../examples/tutorial/solutions/sol_02_sct_lex.ma)

---

## 1. Beyond Single-Argument Structural Recursion

Before introducing `Size`, Mugda already includes a powerful **Size-Change Termination (SCT)** checker based on Lee, Jones, and Ben-Amram (POPL 2001), extended in Karl Mehltretter's thesis (§4.6) to the **matrix semiring $\text{ORDER}_+$** (`Order = Lt | Le | Un | Mat (Matrix Order)` in [`Mugda/Core.lean`](../Mugda/Core.lean#L547-L552)).

For every recursive call $f(p_1, \dots, p_n) \to g(e_1, \dots, e_m)$, Mugda computes an $n \times m$ call matrix whose $(i, j)$ entry records whether argument $e_j$ is:
- **`<` (`Lt`)**: a strict subterm of pattern $p_i$,
- **`<=` (`Le`)**: equal to pattern $p_i$,
- **`?` (`Un`)**: unknown relation, or
- **`Mat M`**: a nested sub-matrix comparing constructor sub-components of $p_i$ and $e_j$.

Mugda then computes the Kleene-star transitive closure of the call graph and checks that **every idempotent self-loop $M = M \cdot M$ has at least one `<` (`Lt`) on its diagonal** (verified in [`checkIdem_sound`](../Mugda/Metatheory.lean#L748) and [`checkAll_sound`](../Mugda/Metatheory.lean#L759)).

---

## 2. What SCT Proves Automatically (0 Size Annotations)

All of the following in [`02_termination.ma`](../examples/tutorial/02_termination.ma) pass with **zero `Size` annotations**:

1. **Permuted arguments (`add2`):**
   ```mugda
   fun add2 : Nat -> Nat -> Nat {
     add2 x zero     = x ;
     add2 x (succ y) = succ (add2 y x)
   }
   ```
   A single call permutes $x$ and $y$ with matrix $\begin{pmatrix} ? & \le \\ < & ? \end{pmatrix}$, whose square $\begin{pmatrix} < & ? \\ ? & < \end{pmatrix}$ is idempotent with `<` on both diagonal entries!
2. **Lexicographic recursion (`ack`):** Ackermann's function `ack (succ x) (succ y) = ack x (ack (succ x) y)`.
3. **Nested constructor patterns via `ORDER_+` (`addpair`, `ackp`):**
   ```mugda
   fun addpair : Pair -> Nat {
     addpair (pair x zero)     = x ;
     addpair (pair x (succ y)) = succ (addpair (pair x y))
   }
   ```
   Even though `pair x y` is a freshly constructed `Pair`, the `ORDER_+` matrix entry tracks the $2 \times 2$ component matrix $\begin{pmatrix} \le & ? \\ ? & < \end{pmatrix}$ inside the single `Pair` argument!
4. **Mutual recursion (`even` / `odd`).**

---

## 3. Where Pure SCT Breaks Down

Syntactic SCT can only compare a recursive call argument against **subterms of the input patterns**. As soon as a recursive call passes the **result of another function call**, the call-matrix entry becomes `?` (`Un`), and SCT rejects the function with `Termination check fails`:

- **Euclidean division (`div` in [`02_div_bad.ma`](../examples/tutorial/02_div_bad.ma)):**
  ```mugda
  fun div : Nat -> Nat -> Nat {
    div zero     y = zero ;
    div (succ x) y = succ (div (minus x y) y)
  }
  ```
  Why does `div` terminate? Because `minus x y` is always $\le x < \text{succ } x$. But syntactically, `minus x y` is an arbitrary function call, not a subterm of `succ x`!
- **Euclid's GCD ([`02_gcd_bad.ma`](../examples/tutorial/02_gcd_bad.ma))** and **Quicksort ([`02_quicksort_bad.ma`](../examples/tutorial/02_quicksort_bad.ma)):** `partition` returns a pair of filtered lists whose lengths are $\le$ the input list, which syntactic subterm comparison cannot see.

To express *"this helper function returns a value no larger than its input"* in the type system itself, we need **Sized Types** (Chapter 3).

---

## 4. Exercises

1. Write `half : Nat -> Nat` (`half (succ (succ n)) = succ (half n)`) and verify that SCT accepts it.
2. Write a 2-argument countdown `lexCount : Nat -> Nat -> Nat` where `lexCount (succ x) zero = succ (lexCount x (succ (succ zero)))` and `lexCount (succ x) (succ y) = succ (lexCount (succ x) y)`.

Compare your answers with [`examples/tutorial/solutions/sol_02_sct_lex.ma`](../examples/tutorial/solutions/sol_02_sct_lex.ma).
