-- Tutorial chapter 2: Termination without sizes
-- Expect: reject (termination)
-- Division by repeated subtraction on unsized natural numbers. It
-- terminates, but the recursive call is on `minus x y`, and the checker
-- only sees an opaque function call where a smaller argument was
-- expected. The order it computes for `minus x y` against the pattern
-- `succ x` is "?" (unknown), so the call matrix has no strict decrease.
-- Chapter 3 fixes this with sized types.

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

fun minus : Nat -> Nat -> Nat
{
  minus zero     y        = zero;
  minus (succ x) zero     = succ x;
  minus (succ x) (succ y) = minus x y
}

-- div x y computes ceiling (x / (y+1))
fun div : Nat -> Nat -> Nat
{
  div zero     y = zero;
  div (succ x) y = succ (div (minus x y) y)
}
