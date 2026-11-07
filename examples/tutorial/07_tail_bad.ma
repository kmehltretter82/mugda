-- Tutorial chapter 7: Coinduction
-- Expect: reject (admissibility)
-- Fibonacci "a la Haskell": fibs = 1 : 1 : zipWith (+) fibs (tail fibs).
-- Writing it with sized types needs a sized `tail : Stream ($ i) -> Stream i`
-- and a `zipWith` on sized streams. Both type-check and the size-change
-- check passes, but neither type is admissible: Mugda allows a size
-- variable in an argument type only when that argument is a sized
-- *inductive* type of exactly that size. The checker reports
-- "tail : type not admissible" and "zipWith : type not admissible". Under
-- Mugda's eager evaluation this restriction matters: evaluating the
-- argument `tail Nat i (fibs ($ i))` while unfolding `fibs` forces `fibs`
-- again (thesis, "Fibonacci a la Haskell").

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

fun add : Nat -> Nat -> Nat
{
  add zero     y = y;
  add (succ x) y = succ (add x y)
}

sized codata Stream (+ A : Set) : Size -> Set
{
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

fun tail : (A : Set) -> (i : Size) -> Stream A ($ i) -> Stream A i
{
  tail A i (scons .A .i x xs) = xs
}

cofun zipWith : (A : Set) -> (B : Set) -> (C : Set) -> (A -> B -> C) ->
                (i : Size) -> Stream A i -> Stream B i -> Stream C i
{
  zipWith A B C f ($ i) (scons .A .i a as) (scons .B .i b bs) =
    scons C i (f a b) (zipWith A B C f i as bs)
}

cofun fibs : (i : Size) -> Stream Nat i
{
  fibs ($ ($ i)) =
    scons Nat ($ i) (succ zero)
      (scons Nat i (succ zero)
        (zipWith Nat Nat Nat add i (fibs i) (tail Nat i (fibs ($ i)))))
}
