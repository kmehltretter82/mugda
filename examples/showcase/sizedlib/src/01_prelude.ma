
----------------------------------------------------------------------
-- Part 1: Prelude
--
-- Basic data types, propositional equality and a few lemmas.  Mugda has
-- no implicit arguments, so every type parameter (and every size) is
-- passed explicitly, also to constructors: `cons A x xs`, `refl A a`.
-- There are no namespaces either, so constructor names must be globally
-- unique: plain lists use nil/cons, sized lists snil/scons, and so on.
----------------------------------------------------------------------

data Bool : Set
{
  tt : Bool;
  ff : Bool
}

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt x y = x;
  ite A ff x y = y
}

fun not : Bool -> Bool
{
  not tt = ff;
  not ff = tt
}

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

let n0 : Nat = zero
let n1 : Nat = succ n0
let n2 : Nat = succ n1
let n3 : Nat = succ n2
let n4 : Nat = succ n3
let n5 : Nat = succ n4
let n6 : Nat = succ n5
let n7 : Nat = succ n6
let n8 : Nat = succ n7
let n9 : Nat = succ n8

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

fun leq : Nat -> Nat -> Bool
{
  leq zero     y        = tt;
  leq (succ x) zero     = ff;
  leq (succ x) (succ y) = leq x y
}

fun isZero : Nat -> Bool
{
  isZero zero     = tt;
  isZero (succ x) = ff
}

-- Sized natural numbers.  `SNat i` contains the numbers below size i;
-- `SNat #` is the full type.
sized data SNat : Size -> Set
{
  szero : (i : Size) -> SNat ($ i);
  ssucc : (i : Size) -> SNat i -> SNat ($ i)
}

fun toNat : (i : Size) -> SNat i -> Nat
{
  toNat .($ i) (szero i)   = zero;
  toNat .($ i) (ssucc i x) = succ (toNat i x)
}

fun fromNat : Nat -> SNat #
{
  fromNat zero     = szero #;
  fromNat (succ x) = ssucc # (fromNat x)
}

data Maybe (+ A : Set) : Set
{
  nothing : Maybe A;
  just    : A -> Maybe A
}

data Prod (+ A : Set) (+ B : Set) : Set
{
  pair : A -> B -> Prod A B
}

fun fst : (A : Set) -> (B : Set) -> Prod A B -> A
{
  fst .A .B (pair A B a b) = a
}

fun snd : (A : Set) -> (B : Set) -> Prod A B -> B
{
  snd .A .B (pair A B a b) = b
}

-- Dependent pairs.
data Sigma (A : Set) (B : A -> Set) : Set
{
  sigma : (a : A) -> B a -> Sigma A B
}

fun proj1 : (A : Set) -> (B : A -> Set) -> Sigma A B -> A
{
  proj1 .A .B (sigma A B a b) = a
}

fun proj2 : (A : Set) -> (B : A -> Set) -> (p : Sigma A B) -> B (proj1 A B p)
{
  proj2 .A .B (sigma A B a b) = b
}

----------------------------------------------------------------------
-- Propositional equality
----------------------------------------------------------------------

data Eq (A : Set) : A -> A -> Set
{
  refl : (a : A) -> Eq A a a
}

fun sym : (A : Set) -> (a : A) -> (b : A) -> Eq A a b -> Eq A b a
{
  sym .A .a .a (refl A a) = refl A a
}

fun trans : (A : Set) -> (a : A) -> (b : A) -> (c : A) ->
            Eq A a b -> Eq A b c -> Eq A a c
{
  trans .A .a .a c (refl A a) q = q
}

fun cong : (A : Set) -> (B : Set) -> (f : A -> B) -> (a : A) -> (b : A) ->
           Eq A a b -> Eq B (f a) (f b)
{
  cong .A B f .a .a (refl A a) = refl B (f a)
}

fun subst : (A : Set) -> (P : A -> Set) -> (a : A) -> (b : A) ->
            Eq A a b -> P a -> P b
{
  subst .A P .a .a (refl A a) p = p
}

-- 0 is a right unit of addition (needs induction: add recurses on
-- its first argument).
fun plus_zero : (n : Nat) -> Eq Nat (add n zero) n
{
  plus_zero zero     = refl Nat zero;
  plus_zero (succ n) = cong Nat Nat succ (add n zero) n (plus_zero n)
}

fun plus_succ : (n : Nat) -> (m : Nat) -> Eq Nat (add n (succ m)) (succ (add n m))
{
  plus_succ zero     m = refl Nat (succ m);
  plus_succ (succ n) m = cong Nat Nat succ (add n (succ m)) (succ (add n m)) (plus_succ n m)
}

fun plus_comm : (n : Nat) -> (m : Nat) -> Eq Nat (add n m) (add m n)
{
  plus_comm zero     m = sym Nat (add m zero) m (plus_zero m);
  plus_comm (succ n) m =
    trans Nat (succ (add n m)) (succ (add m n)) (add m (succ n))
      (cong Nat Nat succ (add n m) (add m n) (plus_comm n m))
      (sym Nat (add m (succ n)) (succ (add m n)) (plus_succ m n))
}

fun plus_assoc : (a : Nat) -> (b : Nat) -> (c : Nat) ->
                 Eq Nat (add (add a b) c) (add a (add b c))
{
  plus_assoc zero     b c = refl Nat (add b c);
  plus_assoc (succ a) b c =
    cong Nat Nat succ (add (add a b) c) (add a (add b c)) (plus_assoc a b c)
}

----------------------------------------------------------------------
-- Plain lists and their algebra
----------------------------------------------------------------------

data List (+ A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

fun append : (A : Set) -> List A -> List A -> List A
{
  append .A (nil A)       ys = ys;
  append .A (cons A x xs) ys = cons A x (append A xs ys)
}

fun length : (A : Set) -> List A -> Nat
{
  length .A (nil A)       = zero;
  length .A (cons A x xs) = succ (length A xs)
}

fun map : (A : Set) -> (B : Set) -> (A -> B) -> List A -> List B
{
  map .A B f (nil A)       = nil B;
  map .A B f (cons A x xs) = cons B (f x) (map A B f xs)
}

fun append_nil : (A : Set) -> (xs : List A) -> Eq (List A) (append A xs (nil A)) xs
{
  append_nil .A (nil A)       = refl (List A) (nil A);
  append_nil .A (cons A x xs) =
    cong (List A) (List A) (cons A x) (append A xs (nil A)) xs (append_nil A xs)
}

fun append_assoc : (A : Set) -> (xs : List A) -> (ys : List A) -> (zs : List A) ->
  Eq (List A) (append A (append A xs ys) zs) (append A xs (append A ys zs))
{
  append_assoc .A (nil A)       ys zs = refl (List A) (append A ys zs);
  append_assoc .A (cons A x xs) ys zs =
    cong (List A) (List A) (cons A x)
         (append A (append A xs ys) zs) (append A xs (append A ys zs))
         (append_assoc A xs ys zs)
}

fun length_append : (A : Set) -> (xs : List A) -> (ys : List A) ->
  Eq Nat (length A (append A xs ys)) (add (length A xs) (length A ys))
{
  length_append .A (nil A)       ys = refl Nat (length A ys);
  length_append .A (cons A x xs) ys =
    cong Nat Nat succ (length A (append A xs ys)) (add (length A xs) (length A ys))
         (length_append A xs ys)
}

----------------------------------------------------------------------
-- Sized lists.  `SList A i` has length below i.
----------------------------------------------------------------------

sized data SList (+ A : Set) : Size -> Set
{
  snil  : (i : Size) -> SList A ($ i);
  scons : (i : Size) -> A -> SList A i -> SList A ($ i)
}

fun fromList : (A : Set) -> List A -> SList A #
{
  fromList .A (nil A)       = snil A #;
  fromList .A (cons A x xs) = scons A # x (fromList A xs)
}

fun toList : (A : Set) -> (i : Size) -> SList A i -> List A
{
  toList .A .($ i) (snil A i)       = nil A;
  toList .A .($ i) (scons A i x xs) = cons A x (toList A i xs)
}

-- Size-preserving map: the result has (at most) the size of the input.
fun smap : (A : Set) -> (B : Set) -> (A -> B) -> (i : Size) -> SList A i -> SList B i
{
  smap .A B f .($ i) (snil A i)       = snil B i;
  smap .A B f .($ i) (scons A i x xs) = scons B i (f x) (smap A B f i xs)
}

fun sappend : (A : Set) -> (i : Size) -> SList A i -> SList A # -> SList A #
{
  sappend .A .($ i) (snil A i)       ys = ys;
  sappend .A .($ i) (scons A i x xs) ys = scons A # x (sappend A i xs ys)
}

----------------------------------------------------------------------
-- Decimal display.  Mugda prints values as terms, so a Nat like 13 is
-- printed as 13 nested `succ`s.  For readable `eval` output we convert
-- results to two decimal digits: `toDec 13` prints as `(dec d1 d3)`.
----------------------------------------------------------------------

data Digit : Set
{
  d0 : Digit; d1 : Digit; d2 : Digit; d3 : Digit; d4 : Digit;
  d5 : Digit; d6 : Digit; d7 : Digit; d8 : Digit; d9 : Digit
}

-- tens and ones; counts modulo 100
data Dec : Set
{
  dec : Digit -> Digit -> Dec
}

fun nextDigit : Digit -> Digit
{
  nextDigit d0 = d1; nextDigit d1 = d2; nextDigit d2 = d3; nextDigit d3 = d4;
  nextDigit d4 = d5; nextDigit d5 = d6; nextDigit d6 = d7; nextDigit d7 = d8;
  nextDigit d8 = d9; nextDigit d9 = d0
}

fun isNine : Digit -> Bool
{
  isNine d0 = ff; isNine d1 = ff; isNine d2 = ff; isNine d3 = ff; isNine d4 = ff;
  isNine d5 = ff; isNine d6 = ff; isNine d7 = ff; isNine d8 = ff; isNine d9 = tt
}

fun incDec : Dec -> Dec
{
  incDec (dec t o) = ite Dec (isNine o) (dec (nextDigit t) d0) (dec t (nextDigit o))
}

fun toDec : Nat -> Dec
{
  toDec zero     = dec d0 d0;
  toDec (succ n) = incDec (toDec n)
}

let decs : List Nat -> List Dec = map Nat Dec toDec

-- A Nat list used by the evaluation examples below: [3,1,4,1,5,9,2,6]
let digits : List Nat =
  cons Nat n3 (cons Nat n1 (cons Nat n4 (cons Nat n1 (cons Nat n5
    (cons Nat n9 (cons Nat n2 (cons Nat n6 (nil Nat))))))))

eval let digits_len : Dec = toDec (length Nat digits)

-- A proof by computation: both sides normalise to 16.
let len_proof : Eq Nat (length Nat (append Nat digits digits)) (add n8 n8)
  = refl Nat (add n8 n8)

-- The same fact from the general lemma, for an arbitrary second list.
let len_digits_append : (ys : List Nat) ->
    Eq Nat (length Nat (append Nat digits ys)) (add n8 (length Nat ys))
  = \ ys -> length_append Nat digits ys
