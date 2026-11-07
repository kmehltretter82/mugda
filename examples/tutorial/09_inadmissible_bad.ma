-- Tutorial chapter 9: Pitfalls and soundness
-- Expect: reject (admissibility)
-- Every size variable `i : Size` in an inductive `fun` telescope must appear as the
-- direct size index of at least one sized inductive domain argument (`SNat i`), and
-- the return type must be monotone in `i`. Here `SNat ($ i)` has index `$ i` rather
-- than `i`, so `szCheckIndFun` reports "shrink : type not admissible".

sized data SNat : Size -> Set {
  zero : (i : Size) -> SNat ($ i) ;
  succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun shrink : (i : Size) -> SNat ($ i) -> SNat i {
  shrink .i (zero i)   = zero i ;
  shrink .i (succ i x) = x
}
