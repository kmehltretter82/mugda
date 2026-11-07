-- Tutorial solutions: Chapter 2 (Size-Change Termination exercises)
-- Expect: accept
-- Solutions to Chapter 2 exercises: mutual `isEven`/`isOdd`, `half`, and
-- lexicographic pair countdown `lexCount`.

data Bool : Set {
  tt : Bool ;
  ff : Bool
}

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

fun add : Nat -> Nat -> Nat {
  add zero y     = y ;
  add (succ x) y = succ (add x y)
}

mutual {
  fun isEven : Nat -> Bool {
    isEven zero     = tt ;
    isEven (succ n) = isOdd n
  }

  fun isOdd : Nat -> Bool {
    isOdd zero     = ff ;
    isOdd (succ n) = isEven n
  }
}

fun half : Nat -> Nat {
  half zero            = zero ;
  half (succ zero)     = zero ;
  half (succ (succ n)) = succ (half n)
}

fun lexCount : Nat -> Nat -> Nat {
  lexCount zero zero            = zero ;
  lexCount zero (succ y)        = succ (lexCount zero y) ;
  lexCount (succ x) zero        = succ (lexCount x (succ (succ zero))) ;
  lexCount (succ x) (succ y)    = succ (lexCount (succ x) y)
}

let n4 : Nat = succ (succ (succ (succ zero)))
eval let half4 : Nat = half n4
eval let even4 : Bool = isEven n4
eval let lex_1_1 : Nat = lexCount (succ zero) (succ zero)
