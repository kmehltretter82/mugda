-- Tutorial chapter 7: Coinduction
-- Expect: reject (termination/productivity)
-- The simplest unproductive stream: `unp i = unp i` never produces a
-- constructor. It type-checks, but the corecursive call is at the same
-- size `i`, so the call matrix is (<=), which is not decreasing, and the
-- checker reports "Termination check fails". (For a cofun this message
-- means "productivity check fails".)

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
  unp i = unp i
}
