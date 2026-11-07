-- Tutorial chapter 9: Pitfalls and soundness
-- Expect: reject (size pattern incomplete)
-- An inductive `fun` cannot pattern-match on a non-dotted successor size `($ i)`
-- because sizes are erased to `#` at runtime (`$ # = #`). The completeness check
-- (`completePatterns` / `cp`) rejects `badPred` with "size pattern incomplete".

sized data SNat : Size -> Set {
  zero : (i : Size) -> SNat ($ i) ;
  succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun badPred : (i : Size) -> SNat i -> SNat i {
  badPred ($ i) (zero .i)   = zero i ;
  badPred ($ i) (succ .i x) = succ i x
}
