-- Tutorial solutions: Chapter 7 (Coinductive stream interleave & evens exercises)
-- Expect: accept
-- Solutions to Chapter 7 exercises: productive stream `interleave` and `evens`
-- on sized coinductive `Stream`.

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

sized codata Stream (+ A : Set) : Size -> Set {
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

fun shead : (A : Set) -> Stream A # -> A {
  shead A (scons .A .# x xs) = x
}

fun stail : (A : Set) -> Stream A # -> Stream A # {
  stail A (scons .A .# x xs) = xs
}

cofun natsFrom : Nat -> (i : Size) -> Stream Nat i {
  natsFrom n ($ i) = scons Nat i n (natsFrom (succ n) i)
}

cofun interleave : (A : Set) -> (i : Size) -> Stream A # -> Stream A # -> Stream A i {
  interleave A ($ i) (scons .A .# x xs) ys = scons A i x (interleave A i ys xs)
}

cofun evens : (A : Set) -> (i : Size) -> Stream A # -> Stream A i {
  evens A ($ i) (scons .A .# x (scons .A .# y xs)) = scons A i x (evens A i xs)
}

let nats : Stream Nat # = natsFrom zero #
let evs  : Stream Nat # = evens Nat # nats

eval let ev2 : Nat = shead Nat (stail Nat (stail Nat evs))
