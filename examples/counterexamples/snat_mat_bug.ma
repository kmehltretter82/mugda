-- Counterexample 4: 1-step SNat counterexample to both the pattern-refinement invariant
-- (Bug 1) and the Matrix-Shaped Extended Order ORDER_+ (Bug 3, Thesis Section 4.6).
--
-- Uses ONLY `SNat` (`zero` and `succ`), no higher-order constructors or auxiliary types.
-- In unpatched Mugda 2008:
--   1. Matching the first argument `(succ .($ ($ i)) (succ .($ i) (succ i z)))` refines
--      the shared size variable to `($ ($ ($ i)))`, forcing `w : SNat ($ i)` in the
--      second argument `(succ .($ ($ i)) (succ .($ i) w))`.
--   2. In `Termination.hs`, `comparePattern` compares the 2-arg `succ` call terms against
--      the 2-arg `succ` patterns using `Mat`, finding `Lt` on the dot-pattern size index
--      `($ i) < ($ ($ i))` while the term argument `w` is `Un`, so `isDecr (Mat m)`
--      returns `True`!
--   3. At runtime, `loop # s3 s3` reduces in 1 step to `loop # s3 s3` and loops forever.
--
-- Rejected in bug-fixed Mugda by both `checkNoccDomains` (Bug 1) and the restriction of
-- `Mat` in `comparePattern` to pure non-sized constructors without dot patterns (Bug 3).

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

let s0 : SNat # = zero #
let s1 : SNat # = succ # s0
let s2 : SNat # = succ # s1
let s3 : SNat # = succ # s2
