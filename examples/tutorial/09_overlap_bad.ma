-- Tutorial chapter 9: Pitfalls and soundness
-- Expect: reject (type error: eqVal error)
-- Overlapping clauses (`isz zero = tt; isz x = ff`) evaluated on an open variable `n`.
-- Because 3-valued `matchPat` returns `stuck` (not `mismatch`) when `ConP "zero"` meets
-- the neutral variable `n`, `matchClauses` refuses to fall through to `isz x = ff`,
-- so `isz n` stays neutral and `bad` is rejected with `eqVal error`.

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
