-- Counterexample 4: SNat counterexample to both the Pattern-Refinement Invariant
-- (Bug 1) and the Matrix-Shaped Extended Order ORDER_+ (Bug 3, Thesis Section 4.6).
--
-- Uses ONLY `SNat` (`zero` and `succ`), no higher-order constructors or auxiliary types.
-- In unpatched Mugda 2008:
--   1. Matching the first argument `(succ .($ ($ i)) (succ .($ i) (succ i z)))` refines
--      the shared size variable to `($ ($ ($ i)))`, forcing `w : SNat ($ i)` in the
--      second argument `(succ .($ ($ i)) (succ .($ i) w))`.
--   2. In `Termination.hs`, `compareExpr` compares the 2-arg `succ` call `(succ ($ i) w)`
--      against the 2-arg `succ` pattern `(succ .($ ($ i)) ...)` using a 2x2 `Mat`,
--      finding `Lt` on the dot-pattern size index `($ i) < ($ ($ i))` while the term
--      argument `w` is `Un`, so `isDecr (Mat m)` returns `True`!
--
-- Rejected in bug-fixed Mugda by both `checkNoccDomains` (Bug 1) and the restriction of
-- `Mat` in `compareExpr` to pure non-sized constructors without dot patterns (Bug 3).

sized data SNat : Size -> Set
{ zero : (i : Size) -> SNat ($ i)
; succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun loop : (i : Size) -> SNat i -> SNat i -> SNat #
{ loop .($ ($ ($ i)))
       (succ .($ ($ i)) (succ .($ i) (succ i z)))
       (succ .($ ($ i)) (succ .($ i) w))
  = loop ($ ($ ($ i)))
         (succ ($ i) w)
         (succ ($ ($ i)) (succ ($ i) w))
; loop i x y = x
}
