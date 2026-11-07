-- Counterexample 3: Self-contained 1-step diverging counterexample using `O`
-- WITHOUT any `Wrap` type or `pre` function!
--
-- Shows how combining:
--   1. Sibling pattern refinement on `M .($ ($ i)) (L .($ i) f) (S .($ i) (S i z))` (Bug 1), and
--   2. The Extended Matrix Order `ORDER_+` on `M` (Bug 3)
-- allows a 1-clause function `loop : (i : Size) -> O i -> O i -> Nat` with a completely
-- admissible signature to pass unpatched Mugda 2008 with zero warnings and diverge
-- in a 1-step cycle!
--
-- How it works:
--   - `emb : Nat -> O #` maps `two` to `S # (S # (Z #))`.
--   - `g0 : Nat -> O # = \n -> L # emb` is a non-recursive constant function returning `L # emb`.
--   - In `loop`, Call Arg 1 is `M ($ i) (g zero) (f two)`, whose first component `($ i)` is
--     strictly smaller (`Lt`) than `.($ ($ i))` in Pattern 1's `M`, so Mugda 2008's `Mat`
--     order sees `Lt` at (1,1) of the diagonal!
--   - At runtime, `g0 zero` evaluates to `L # emb` and `emb two` evaluates to `S # (S # (Z #))`,
--     so `loop # term1 term2` reduces in 1 step to `loop # term1 term2` and loops forever!
--
-- Rejected in bug-fixed Mugda by both `checkNoccDomains` (Bug 1) and the `ORDER_+`
-- restriction in `Termination.hs` (Bug 3).

data Nat : Set
{ zero : Nat
; succ : Nat -> Nat
}

let two : Nat = succ (succ zero)

sized data O : Size -> Set
{ Z : (i : Size) -> O ($ i)
; S : (i : Size) -> O i -> O ($ i)
; L : (i : Size) -> (Nat -> O i) -> O ($ i)
; M : (i : Size) -> O i -> O i -> O ($ i)
}

fun emb : Nat -> O #
{ emb zero = Z #
; emb (succ n) = S # (emb n)
}

let g0 : Nat -> O # = \n -> L # emb

fun loop : (i : Size) -> O i -> O i -> Nat
{ loop .($ ($ ($ i)))
       (M .($ ($ i)) (L .($ i) f) (S .($ i) (S i z)))
       (M .($ ($ i)) (L .($ i) g) (S .($ i) w))
    = loop ($ ($ ($ i)))
           (M ($ i) (g zero) (f two))
           (M ($ ($ i)) (L ($ i) g) (f two))
; loop i x y = zero
}

let term1 : O # = M # (L # emb) (emb two)
let term2 : O # = M # (L # g0) (emb two)
eval let diverge : Nat = loop # term1 term2
