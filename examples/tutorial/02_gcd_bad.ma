-- Tutorial chapter 2: Termination without sizes
-- Expect: reject (termination)
-- Euclid's algorithm by repeated subtraction on unsized naturals. Both
-- recursive calls pass a `minus` result, whose relation to the input the
-- checker cannot see, so it reports "Termination check fails" even though
-- the function terminates. The sized version in chapter 3 is accepted.

data Bool : Set
{
  tt : Bool;
  ff : Bool
}

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

fun le : Nat -> Nat -> Bool
{
  le zero     y        = tt;
  le (succ x) zero     = ff;
  le (succ x) (succ y) = le x y
}

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt a b = a;
  ite A ff a b = b
}

fun gcd : Nat -> Nat -> Nat
{
  gcd zero     y        = y;
  gcd (succ x) zero     = succ x;
  gcd (succ x) (succ y) =
    ite Nat (le x y)
        (gcd (succ x) (minus y x))
        (gcd (minus x y) (succ y))
}
