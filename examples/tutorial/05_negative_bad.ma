-- Tutorial chapter 5: Subtyping and variance
-- Expect: reject (strict positivity)
-- The untyped lambda calculus as a data type (thesis Fig. 3.10). Term
-- occurs to the left of an arrow in the argument of `abs`. If this were
-- accepted, `app` would pass the termination check (it is not even
-- recursive), and yet `diverge` below would loop forever. Mugda rejects the
-- data declaration: "rec. arg not strictly positive".

data Term : Set
{
  abs : (Term -> Term) -> Term
}

fun app : Term -> Term -> Term
{
  app (abs f) y = f y
}

let omega   : Term = abs (\ x -> app x x)
let diverge : Term = app omega omega
