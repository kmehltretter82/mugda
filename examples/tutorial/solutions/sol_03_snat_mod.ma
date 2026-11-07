-- Tutorial solutions: Chapter 3 (Sized SNat modulo & division exercises)
-- Expect: accept
-- Solutions to Chapter 3 exercises: size-preserving `minus` and Euclidean
-- remainder `mod` on sized natural numbers `SNat`.

data Bool : Set {
  tt : Bool ;
  ff : Bool
}

sized data SNat : Size -> Set {
  zero : (i : Size) -> SNat ($ i) ;
  succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun leq : SNat # -> SNat # -> Bool {
  leq (zero .#) y                   = tt ;
  leq (succ .# x) (zero .#)         = ff ;
  leq (succ .# x) (succ .# y)       = leq x y
}

fun minus : (i : Size) -> SNat i -> SNat # -> SNat i {
  minus .($ i) (zero i) y                   = zero i ;
  minus .($ i) (succ i x) (zero .#)         = succ i x ;
  minus .($ i) (succ i x) (succ .# y)       = minus i x y
}

fun modAux : (i : Size) -> Bool -> SNat i -> SNat # -> SNat # {
  modAux i      ff x y          = x ;
  modAux .($ i) tt (zero i) y   = zero # ;
  modAux .($ i) tt (succ i x) y =
    let r : SNat i = minus i x y in
    modAux i (leq (succ # y) r) r y
}

let s0 : SNat # = zero #
let s1 : SNat # = succ # s0
let s2 : SNat # = succ # s1
let s3 : SNat # = succ # s2
let s7 : SNat # = succ # (succ # (succ # (succ # s3)))

eval let mod_7_3 : SNat # = modAux # (leq s3 s7) s7 s2
