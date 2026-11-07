-- Tutorial chapter 3: Sized inductive types
-- Expect: reject (termination)
-- Sizes only help when they carry information. Here `minus` is given the
-- weaker type `SNat i -> SNat # -> SNat #`: it is still correct, but the
-- caller no longer learns that the result is bounded by `i`. `div` must
-- then call itself at size `#`, and the call matrix compares `#` with the
-- pattern `.($ i)`, which yields "?" (unknown). No argument decreases, so
-- the termination check fails, exactly as in the unsized version of
-- chapter 2.

sized data SNat : Size -> Set
{
  zero : (i : Size) -> SNat ($ i);
  succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun minus : (i : Size) -> SNat i -> SNat # -> SNat #
{
  minus .($ i) (zero i)   y           = zero i;
  minus .($ i) (succ i x) (zero .#)   = succ i x;
  minus .($ i) (succ i x) (succ .# y) = minus i x y
}

fun div : (i : Size) -> SNat i -> SNat # -> SNat #
{
  div .($ i) (zero i)   y           = zero i;
  div .($ i) (succ i x) (zero .#)   = zero i;
  div .($ i) (succ i x) (succ .# y) = succ # (div # (minus i x y) (succ # y))
}
