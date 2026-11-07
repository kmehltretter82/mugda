-- Tutorial chapter 2: Termination without sizes
-- Expect: reject (termination)
-- A function that really does loop: bad (pair 1 1) calls bad (pair 2 0),
-- which calls bad (pair 1 1) again. The size-change checker finds the
-- idempotent call matrix with no strict decrease on its diagonal and
-- prints "Termination check fails". Type checking itself succeeds, so the
-- evaluator still runs, but a function that failed the check is never
-- unfolded: `loop` evaluates to the stuck term `bad (pair ...)`.

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

data Pair : Set
{
  pair : Nat -> Nat -> Pair
}

fun bad : Pair -> Nat
{
  bad (pair zero zero)     = zero;
  bad (pair x (succ y))    = bad (pair (succ x) y);
  bad (pair (succ x) zero) = bad (pair x (succ zero))
}

eval let loop : Nat = bad (pair (succ zero) (succ zero))
