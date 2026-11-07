-- Tutorial chapter 5: Subtyping and variance
-- Expect: reject (type error: subtyping)
-- Sizes of inductive types are upper bounds, so subtyping goes one way
-- only: SNat i <= SNat #, but not SNat # <= SNat i. A function claiming
-- to shrink an arbitrary number to any size `i`, using nothing but the
-- identity, is rejected. The checker's message is "leqSize error": it
-- could not show # <= i.

sized data SNat : Size -> Set
{
  zero : (i : Size) -> SNat ($ i);
  succ : (i : Size) -> SNat i -> SNat ($ i)
}

let shrink : (i : Size) -> SNat # -> SNat i = \ i -> \ n -> n
