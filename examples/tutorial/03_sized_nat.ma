-- Tutorial chapter 3: Sized inductive types
-- Expect: accept
-- Sized natural numbers. `SNat i` holds the numbers whose height is below
-- the size `i`; `$ i` is the successor size and `#` is the "infinite" size
-- that every closed number fits into. The point of the chapter is the type
-- of `minus`: its result is bounded by the size of its first argument.
-- With that information, `div` and `gcd`, which chapter 2 rejected, become
-- size-decreasing recursions that the checker accepts.

sized data SNat : Size -> Set
{
  zero : (i : Size) -> SNat ($ i);
  succ : (i : Size) -> SNat i -> SNat ($ i)
}

-- closed numbers live at size #
let n0 : SNat # = zero #
let n1 : SNat # = succ # n0
let n2 : SNat # = succ # n1
let n3 : SNat # = succ # n2
let n4 : SNat # = succ # n3
let n6 : SNat # = succ # (succ # n4)

-- at size # we can still do ordinary structural recursion;
-- the size argument of the constructor is the dot pattern `.#`
fun add : SNat # -> SNat # -> SNat #
{
  add (zero .#)   y = y;
  add (succ .# x) y = succ # (add x y)
}

-- the size-indexed version: matching `succ i x` against `SNat j` tells the
-- checker that j = $ i (written `.($ i)`), and x : SNat i
fun minus : (i : Size) -> SNat i -> SNat # -> SNat i
{
  minus .($ i) (zero i)   y           = zero i;
  minus .($ i) (succ i x) (zero .#)   = succ i x;
  minus .($ i) (succ i x) (succ .# y) = minus i x y
}

-- `minus i x y : SNat i`, so the recursive call is at size i < $ i
fun div : (i : Size) -> SNat i -> SNat # -> SNat i
{
  div .($ i) (zero i)   y           = zero i;
  div .($ i) (succ i x) (zero .#)   = zero i;
  div .($ i) (succ i x) (succ .# y) = succ i (div i (minus i x y) (succ # y))
}

data Bool : Set
{
  tt : Bool;
  ff : Bool
}

fun le : SNat # -> SNat # -> Bool
{
  le (zero .#)   y           = tt;
  le (succ .# x) (zero .#)   = ff;
  le (succ .# x) (succ .# y) = le x y
}

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt a b = a;
  ite A ff a b = b
}

-- two size arguments; in each recursive call one of them decreases and
-- the other stays the same, a job for the size-change principle
fun gcd : (i : Size) -> (j : Size) -> SNat i -> SNat j -> SNat #
{
  gcd .($ i) j      (zero i)   y          = y;
  gcd .($ i) .($ j) (succ i x) (zero j)   = succ i x;
  gcd .($ i) .($ j) (succ i x) (succ j y) =
    ite (SNat #) (le x y)
        (gcd ($ i) j (succ i x) (minus j y x))
        (gcd i ($ j) (minus i x y) (succ j y))
}

eval let two   : SNat # = minus # n4 n2
eval let three : SNat # = div # n6 n2
eval let gcd64 : SNat # = gcd # # n6 n4
