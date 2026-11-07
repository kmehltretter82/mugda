-- Showcase 2 (Negative): Unproductive Circular Bisimulation Proof
-- Expect: reject (type error: leqVal error)
--
-- If someone tries to prove two arbitrary streams `s1` and `s2` bisimilar by
-- circular coinduction without emitting a `bisimCons` constructor (`badBisim ($ i) = badBisim i`),
-- contravariant subtyping (`Bisim A ($ i) s1 s2 <= Bisim A i s1 s2`, NOT `Bisim A i <= Bisim A ($ i)`)
-- immediately rejects the definition!

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

sized codata Stream (+ A : Set) : Size -> Set
{
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

sized codata Bisim (+ A : Set) : Size -> Stream A # -> Stream A # -> Set
{
  bisimCons : (i : Size) -> (x : A) -> (xs : Stream A #) -> (ys : Stream A #) ->
              Bisim A i xs ys ->
              Bisim A ($ i) (scons A # x xs) (scons A # x ys)
}

cofun badBisim : (A : Set) -> (s1 : Stream A #) -> (s2 : Stream A #) ->
                 (i : Size) -> Bisim A i s1 s2
{
  badBisim A s1 s2 ($ i) = badBisim A s1 s2 i
}
