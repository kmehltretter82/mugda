-- Tutorial solutions: Chapter 1 (Bool & Nat exercises)
-- Expect: accept
-- Solutions to Chapter 1 exercises: boolean `xor`, natural number multiplication
-- `mul`, and exponentiation `exp`.

data Bool : Set {
  tt : Bool ;
  ff : Bool
}

fun xor : Bool -> Bool -> Bool {
  xor tt tt = ff ;
  xor tt ff = tt ;
  xor ff tt = tt ;
  xor ff ff = ff
}

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

fun add : Nat -> Nat -> Nat {
  add zero y     = y ;
  add (succ x) y = succ (add x y)
}

fun mul : Nat -> Nat -> Nat {
  mul zero y     = zero ;
  mul (succ x) y = add y (mul x y)
}

fun exp : Nat -> Nat -> Nat {
  exp b zero     = succ zero ;
  exp b (succ e) = mul b (exp b e)
}

let n2 : Nat = succ (succ zero)
let n3 : Nat = succ n2
eval let xor_tf : Bool = xor tt ff
eval let two_cubed : Nat = exp n2 n3
