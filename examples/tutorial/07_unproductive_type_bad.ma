-- Tutorial chapter 7: Coinduction
-- Expect: reject (type error)
-- The other way to write the unproductive stream: match on `($ i)` and call
-- `unp i`. Now the size decreases, so the termination checker would be
-- satisfied. But the right-hand side has type Stream Nat i, and the clause
-- must return Stream Nat ($ i). For codata, Stream ($ i) <= Stream i, not
-- the other way round, so this is a type error ("leqSize error"). Only a
-- constructor can raise the size of a stream from i to $ i.

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

sized codata Stream (+ A : Set) : Size -> Set
{
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

cofun unp : (i : Size) -> Stream Nat i
{
  unp ($ i) = unp i
}
