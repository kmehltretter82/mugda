# Chapter 5 — Subtyping, Variance (`+` Parameters) & Strict Positivity

**Companion files:**
- Accepted: [`examples/tutorial/05_subtyping.ma`](../examples/tutorial/05_subtyping.ma)
- Rejected: [`05_down_bad.ma`](../examples/tutorial/05_down_bad.ma), [`05_invariant_bad.ma`](../examples/tutorial/05_invariant_bad.ma), [`05_negative_bad.ma`](../examples/tutorial/05_negative_bad.ma), [`05_param_bad.ma`](../examples/tutorial/05_param_bad.ma), [`05_rose_bad.ma`](../examples/tutorial/05_rose_bad.ma)

---

## 1. Variance of Size Indices and Type Parameters

Mugda's subtyping judgment `leqVal` (formally verified in [`Mugda/Soundness.lean` §6](../Mugda/Soundness.lean#L345-L420) and [`Mugda/Metatheory.lean` §3C](../Mugda/Metatheory.lean#L800-L890)) obeys four core variance rules:

| Type Constructor | Variance in Size / Parameter | Subtyping Rule | Lean 4 Theorem |
| :--- | :--- | :--- | :--- |
| **Sized `data` (`Ind`)** | **Covariant** in `i : Size` | $i \le j \implies D\ i \le D\ j$ | [`leqApp_sized_variance`](../Mugda/Metatheory.lean#L834) |
| **Sized `codata` (`CoInd`)** | **Contravariant** in `i : Size` | $j \le i \implies C\ i \le C\ j$ | [`inStream_contravariant`](../Mugda/Soundness.lean#L488), [`leqApp_sized_variance`](../Mugda/Metatheory.lean#L834) |
| **Function type `A -> B`** | **Contravariant** in `A`, **Covariant** in `B` | $A' \le A \wedge B \le B' \implies (A \to B) \le (A' \to B')$ | [`arrow_contravariant`](../Mugda/Soundness.lean#L379), [`arrow_covariant`](../Mugda/Soundness.lean#L372) |
| **Parameter `+ A : Set`** | **Covariant** if marked `+`, **Invariant** otherwise | $A \le A' \implies T(+A) \le T(+A')$ | [`sposConstructor_vpi_inv`](../Mugda/Metatheory.lean#L727) |

In [`05_subtyping.ma`](../examples/tutorial/05_subtyping.ma), every valid coercion is simply the identity lambda `\ x -> x`:

- `up1 : (i : Size) -> SNat i -> SNat ($ i)` (covariant step $i \le \$ i$)
- `upInfty : (i : Size) -> SNat i -> SNat #` (covariant bound $i \le \#$)
- `boxUp : (i : Size) -> Box (SNat i) -> Box (SNat #)` (where `data Box (+ A : Set) : Set`)
- `contraFn : (i : Size) -> (SNat # -> Bool) -> (SNat i -> Bool)` (contravariant domain: a function accepting any `SNat #` can be passed an `SNat i`!)

---

## 2. What Subtyping & Positivity Reject

1. **Downward size coercion on inductive types ([`05_down_bad.ma`](../examples/tutorial/05_down_bad.ma)):**
   `SNat # -> SNat i` fails with `leqSize error` because `# <= i` is false.
2. **Coercing inside an invariant parameter ([`05_invariant_bad.ma`](../examples/tutorial/05_invariant_bad.ma)):**
   When `data Box (A : Set)` omits `+`, `Box (SNat i) -> Box (SNat #)` fails with `eqVal error`.
3. **Negative recursive occurrence ([`05_negative_bad.ma`](../examples/tutorial/05_negative_bad.ma)):**
   `data Term : Set { abs : (Term -> Term) -> Term }` is rejected by `sposConstructor` with `rec. arg not strictly positive` (see [`spos_vpi_inv`](../Mugda/Metatheory.lean#L653)).
4. **Negative occurrence of a `+` parameter ([`05_param_bad.ma`](../examples/tutorial/05_param_bad.ma)):**
   `data Fun (+ A : Set) : Set { mk : (A -> Nat) -> Fun A }` is rejected with `parameter not strictly positive`.
5. **Nested recursion through an invariant container ([`05_rose_bad.ma`](../examples/tutorial/05_rose_bad.ma)):**
   `data Rose (+ A : Set) : Set { node : A -> List (Rose A) -> Rose A }` is rejected if `List` omits `+` on its element parameter, and accepted in [`05_subtyping.ma`](../examples/tutorial/05_subtyping.ma) when `SList (+ A : Set)` declares `+`!
