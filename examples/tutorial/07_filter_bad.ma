-- Tutorial chapter 7: Coinduction
-- Expect: reject (termination/productivity)
-- Filtering a stream is not productive in general: with a predicate that
-- is always false, `sfilter` would search forever for the next element.
-- Mugda rejects it. In the `ff` branch the corecursive call is at the
-- same size `$ i`, and the stream argument `xs` does not count as smaller
-- than `scons .# x xs`, because codata is not well-founded. So no argument
-- decreases.

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

sized codata Stream (+ A : Set) : Size -> Set
{
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt a b = a;
  ite A ff a b = b
}

cofun sfilter : (A : Set) -> (A -> Bool) -> Stream A # -> (i : Size) -> Stream A i
{
  sfilter .A p (scons A .# x xs) ($ i) =
    ite (Stream A ($ i)) (p x)
        (scons A i x (sfilter A p xs i))
        (sfilter A p xs ($ i))
}
