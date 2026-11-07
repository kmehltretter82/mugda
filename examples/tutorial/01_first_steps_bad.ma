-- Tutorial chapter 1: First steps
-- Expect: reject (type error)
-- A deliberately ill-typed program: `not` expects a Bool but is given a
-- Nat. Type errors abort checking immediately; the checker prints
-- "error during typechecking:" followed by the name of the offending
-- declaration and a (terse) reason, and exits with code 1.

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

fun not : Bool -> Bool
{
  not tt = ff;
  not ff = tt
}

let oops : Bool = not zero
