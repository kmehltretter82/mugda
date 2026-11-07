-- Tutorial chapter 5: Subtyping and variance
-- Expect: reject (strict positivity of a parameter)
-- The same trick hidden behind a parameter (thesis Fig. 3.11). `Fun`
-- declares its parameter A strictly positive with `+`, but A occurs to the
-- left of an arrow. Mugda checks the `+` claim and rejects `Fun` with
-- "parameter not strictly positive". Without that check, `Term` would pass
-- (it uses its own type only inside a `+` parameter) and `diverge` would
-- loop.

data Fun (+ A : Set) : Set
{
  func : (A -> A) -> Fun A
}

data Term : Set
{
  abs : Fun Term -> Term
}

fun app : Term -> Term -> Term
{
  app (abs (func .Term f)) y = f y
}

let omega   : Term = abs (func Term (\ x -> app x x))
let diverge : Term = app omega omega
