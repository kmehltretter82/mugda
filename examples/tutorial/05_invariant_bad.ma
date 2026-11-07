-- Tutorial chapter 5: Subtyping and variance
-- Expect: reject (type error: invariant parameter)
-- Without the `+` annotation a data type parameter is invariant: Box A
-- and Box B are related only when A and B are equal. So the coercion
-- Box (SNat i) -> Box (SNat #) fails ("eqVal error"), even though
-- SNat i <= SNat #. Declaring the parameter as `(+ A : Set)` makes this
-- file type-check (see the exercises).

sized data SNat : Size -> Set
{
  zero : (i : Size) -> SNat ($ i);
  succ : (i : Size) -> SNat i -> SNat ($ i)
}

data Box (A : Set) : Set
{
  box : A -> Box A
}

let upBox : (i : Size) -> Box (SNat i) -> Box (SNat #) = \ i -> \ b -> b
