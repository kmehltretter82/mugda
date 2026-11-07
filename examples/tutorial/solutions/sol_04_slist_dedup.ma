-- Tutorial solutions: Chapter 4 (Sized lists filter & take exercises)
-- Expect: accept
-- Solutions to Chapter 4 exercises: size-preserving `sfilter` and `stake` on `SList`.

data Bool : Set {
  tt : Bool ;
  ff : Bool
}

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

sized data SList (+ A : Set) : Size -> Set {
  nil  : (i : Size) -> SList A ($ i) ;
  cons : (i : Size) -> A -> SList A i -> SList A ($ i)
}

fun ite : (A : Set) -> Bool -> A -> A -> A {
  ite A tt x y = x ;
  ite A ff x y = y
}

fun sfilter : (i : Size) -> (A : Set) -> (A -> Bool) -> SList A i -> SList A i {
  sfilter .($ i) A p (nil .A i)       = nil A i ;
  sfilter .($ i) A p (cons .A i x xs) =
    ite (SList A ($ i)) (p x)
      (cons A i x (sfilter i A p xs))
      (sfilter i A p xs)
}

fun isNonZero : Nat -> Bool {
  isNonZero zero     = ff ;
  isNonZero (succ n) = tt
}

let sample : SList Nat # =
  cons Nat # zero (cons Nat # (succ zero) (cons Nat # zero (cons Nat # (succ (succ zero)) (nil Nat #))))

eval let nonzero_only : SList Nat # = sfilter # Nat isNonZero sample
