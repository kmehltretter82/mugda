-- Expect: reject (type error: eqVal error)
--
-- Found while writing sizedlib.  In the original 2008 Mugda (`Value.hs`),
-- `match` returned a 2-valued `Maybe Env`, so matching a constructor pattern
-- against a neutral variable returned `Nothing` and fell through to a later
-- catch-all clause (`isz x = ff`), allowing `bad n = refl Bool ff` to prove
-- `tt = ff`.
--
-- Fixed in `Mugda/Core.lean` via 3-valued `MatchResult` (`matched` | `mismatch` | `stuck`):
-- matching `ConP "zero"` against `.VGen 0` returns `stuck`, halting `matchClauses`
-- and soundly rejecting `bad` with `eqVal error`.

data Nat : Set { zero : Nat; succ : Nat -> Nat }
data Bool : Set { tt : Bool; ff : Bool }
data Eq (A : Set) : A -> A -> Set { refl : (a : A) -> Eq A a a }

fun isz : Nat -> Bool { isz zero = tt; isz x = ff }

-- wrongly accepted: for a variable n, `isz n` is converted to `ff`
fun bad : (n : Nat) -> Eq Bool (isz n) ff { bad n = refl Bool ff }

eval let contra : Eq Bool tt ff = bad zero
