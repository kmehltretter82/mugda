-- Expect: reject (Termination check fails: division and gcd without sizes)
--
-- sdiv and sgcd of sizedlib (src/02_sized.ma) on plain Nat instead of
-- SNat i.  Each recursive call is on `minus x y`, which is not a
-- structural subterm of `succ x`.  In sizedlib the type
-- `sminus : (i : Size) -> SNat i -> SNat # -> SNat i` tells the checker
-- that the result is no bigger than x; here that information is lost.

data Bool : Set
{
  tt : Bool;
  ff : Bool
}

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt x y = x;
  ite A ff x y = y
}

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

fun leq : Nat -> Nat -> Bool
{
  leq zero     y        = tt;
  leq (succ x) zero     = ff;
  leq (succ x) (succ y) = leq x y
}

fun minus : Nat -> Nat -> Nat
{
  minus zero     y        = zero;
  minus (succ x) zero     = succ x;
  minus (succ x) (succ y) = minus x y
}

fun div : Nat -> Nat -> Nat
{
  div zero     y        = zero;
  div (succ x) zero     = zero;
  div (succ x) (succ y) =
    ite Nat (leq (succ x) y) zero (succ (div (minus x y) (succ y)))
}

fun gcd : Nat -> Nat -> Nat
{
  gcd zero     y        = y;
  gcd (succ x) zero     = succ x;
  gcd (succ x) (succ y) =
    ite Nat (leq y x)
        (gcd (minus x y) (succ y))
        (gcd (succ x) (minus y x))
}
