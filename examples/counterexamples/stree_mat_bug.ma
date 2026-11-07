-- Counterexample 5: Sized Binary Tree (STree) counterexample to both the
-- Pattern-Refinement Invariant (Bug 1) and the Extended Matrix Order ORDER_+ (Bug 3).
--
-- In unpatched Mugda 2008:
--   - Matching `node .($ ($ ($ i))) (node .($ ($ i)) (node .($ i) (node i a1 a2) b) c) d`
--     refines the shared size index of `b`, `c`, `d` across sibling branches of `node`.
--   - In `Termination.hs`, `comparePattern` builds a 3x3 `Mat` for `node` whose (1,1)
--     entry compares the size index `($ ($ i)) < .($ ($ ($ i)))` (`Lt`), while `a1` is
--     duplicated into `node i a1 a1`.
--   - Evaluating `loop # t4` in Mugda 2008 reduces in 1 step to `loop # t4` and loops forever!
--
-- Rejected in bug-fixed Mugda by both `checkNoccDomains` (Bug 1) and the restriction of
-- `Mat` in `comparePattern` to pure non-sized constructors without dot patterns (Bug 3).

sized data STree : Size -> Set
{ leaf : (i : Size) -> STree ($ i)
; node : (i : Size) -> STree i -> STree i -> STree ($ i)
}

fun loop : (i : Size) -> STree i -> STree #
{ loop .($ ($ ($ ($ i)))) (node .($ ($ ($ i))) (node .($ ($ i)) (node .($ i) (node i a1 a2) b) c) d)
  = loop ($ ($ ($ ($ i)))) (node ($ ($ i)) (node ($ i) (node i a1 a1) b) c)
; loop i x = x
}

let t0 : STree # = leaf #
let t1 : STree # = node # t0 t0
let t2 : STree # = node # t1 t1
let t3 : STree # = node # t2 t2
let t4 : STree # = node # t3 t3
eval let diverge : STree # = loop # t4
