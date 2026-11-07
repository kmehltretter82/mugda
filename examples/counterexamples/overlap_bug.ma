-- Counterexample 7: Overlapping-clause fallthrough on neutral scrutinees (Value.hs lines 178-222).
-- Expect: reject (type error: eqVal error)
--
-- In original 2008 Mugda (`Value.hs`), `match` returned a 2-valued `Maybe Env` (`Just` vs `Nothing`),
-- conflating a definite constructor mismatch (`zero` vs `succ y`) with neutral stuckness (`zero` vs `.VGen k`).
-- Consequently, when evaluating `isz n` on an open variable `n` against:
--   isz zero = tt ;
--   isz x    = ff
-- Clause 1 returned `Nothing` on `.VGen 0` and `matchClauses` unsoundly fell through to Clause 2,
-- reducing open `isz n` to `ff` (allowing `bad n = refl Bool ff` to type-check) while closed `isz zero`
-- reduced to `tt` — yielding a closed proof `contra : Eq Bool tt ff`!
--
-- With 3-valued `MatchResult` (`matched` | `mismatch` | `stuck`), matching `ConP "zero"` against
-- `.VGen 0` returns `stuck`, halting `matchClauses` and soundly rejecting `bad` with `eqVal error`.

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

data Bool : Set {
  tt : Bool ;
  ff : Bool
}

data Eq (A : Set) : A -> A -> Set {
  refl : (a : A) -> Eq A a a
}

fun isz : Nat -> Bool {
  isz zero = tt ;
  isz x    = ff
}

fun bad : (n : Nat) -> Eq Bool (isz n) ff {
  bad n = refl Bool ff
}

eval let contra : Eq Bool tt ff = bad zero
