-- Tutorial chapter 9: Pitfalls and soundness
-- Expect: accept
-- Safe deep matching on a sized Brouwer ordinal (`O`): each branch of `pair`
-- introduces its own independent size variable (`i1` and `i2`), and the recursive
-- step takes a single constructor peel (`S ($ i) x`), so the Pattern-Refinement
-- Invariant (`checkNoccEnv` + `checkNoccDomains`) is satisfied.

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

fun add : Nat -> Nat -> Nat {
  add zero y = y ;
  add (succ x) y = succ (add x y)
}

sized data O : Size -> Set {
  Z : (i : Size) -> O ($ i) ;
  S : (i : Size) -> O i -> O ($ i) ;
  L : (i : Size) -> (Nat -> O i) -> O ($ i)
}

-- Safe single-step peel on O:
fun stepCount : (i : Size) -> O i -> Nat {
  stepCount .($ i) (Z i)     = zero ;
  stepCount .($ i) (S i x)   = succ (stepCount i x) ;
  stepCount .($ i) (L i f)   = succ (stepCount i (f zero))
}

let o3 : O # = S # (S # (S # (Z #)))
eval let count_o3 : Nat = stepCount # o3
