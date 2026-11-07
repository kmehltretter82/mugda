-- Tutorial chapter 5: Subtyping and variance
-- Expect: reject (strict positivity: parameter not declared +)
-- A rose tree whose children are stored in a list (compare
-- examples/rose.ma). Here List's parameter is not declared `+`, so the
-- checker cannot assume that List preserves strict positivity, and `Rose`
-- is rejected: "rec. arg not strictly positive". Writing
-- `data List (+ A : Set)` fixes it.

data List (A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

data Rose (A : Set) : Set
{
  rose : A -> List (Rose A) -> Rose A
}
