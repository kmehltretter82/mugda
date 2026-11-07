-- Tutorial chapter 1: First steps
-- Expect: accept
-- A first tour of Mugda: inductive data types, recursive functions defined
-- by pattern matching, global lets, local lets, lambdas, and `eval let`.
-- Everything is explicit: there are no implicit arguments, so a polymorphic
-- function takes its type argument like any other argument, and every
-- constructor of a parameterised type takes the parameter first. The file
-- also contains a tiny proof, because Mugda is dependently typed.

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

fun add : Nat -> Nat -> Nat
{
  add zero     y = y;
  add (succ x) y = succ (add x y)
}

fun mul : Nat -> Nat -> Nat
{
  mul zero     y = zero;
  mul (succ x) y = add y (mul x y)
}

-- a plain `let` is checked but not printed
let one   : Nat = succ zero
let two   : Nat = succ one
let three : Nat = add two one

-- an `eval let` is checked and then evaluated
eval let six : Nat = mul two three

-- polymorphism: the type is an ordinary (explicit) argument
fun id : (A : Set) -> A -> A
{
  id A x = x
}

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt x y = x;
  ite A ff x y = y
}

eval let five : Nat = ite Nat (not ff) (add two three) zero

-- lambdas and local lets
let twice : (A : Set) -> (A -> A) -> A -> A = \ A -> \ f -> \ x -> f (f x)

eval let four : Nat =
  let addTwo : Nat -> Nat = \ n -> add two n in
  twice Nat addTwo zero

-- a parameterised data type: constructors take the parameter explicitly
data List (A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

-- `A` is bound by the first pattern, so inside the constructor pattern it
-- must be written as the inaccessible (dot) pattern `.A`
fun length : (A : Set) -> List A -> Nat
{
  length A (nil .A)       = zero;
  length A (cons .A x xs) = succ (length A xs)
}

fun append : (A : Set) -> List A -> List A -> List A
{
  append A (nil .A)       ys = ys;
  append A (cons .A x xs) ys = cons A x (append A xs ys)
}

eval let bools : List Bool =
  append Bool (cons Bool tt (nil Bool)) (cons Bool ff (cons Bool tt (nil Bool)))

eval let len : Nat = length Bool bools

-- propositional equality, as an inductive family
data Eq (A : Set) : A -> A -> Set
{
  refl : (a : A) -> Eq A a a
}

-- `add zero x` reduces to `x` by the first clause of `add`,
-- so `refl` type-checks
let zeroLeft : (x : Nat) -> Eq Nat (add zero x) x = \ x -> refl Nat x

-- `add x zero` is stuck on the variable `x`; we prove it by recursion
fun cong : (x : Nat) -> (y : Nat) -> Eq Nat x y -> Eq Nat (succ x) (succ y)
{
  cong .x .x (refl .Nat x) = refl Nat (succ x)
}

fun zeroRight : (x : Nat) -> Eq Nat (add x zero) x
{
  zeroRight zero     = refl Nat zero;
  zeroRight (succ x) = cong (add x zero) x (zeroRight x)
}
