-- Expect: accept
--
-- SizedLib: a small library and a verified compiler in Mugda.
--
-- GENERATED FILE -- DO NOT EDIT BY HAND.
-- This file is the concatenation of examples/showcase/sizedlib/src/*.ma
-- (Mugda has no imports).  Edit the parts in src/ and regenerate with
--     make showcase
-- or  cat examples/showcase/sizedlib/src/*.ma > examples/showcase/sizedlib/sizedlib.ma
--
-- Parts:
--   01_prelude      Bool, Nat, SNat, Maybe, Prod, Sigma, Eq, List, SList,
--                   equational lemmas, decimal display
--   02_sized        div, gcd, quicksort, merge sort, rose trees, ordinals:
--                   terminating only thanks to sized types
--   03_coinduction  sized streams, stream processors, bisimulation proofs
--   04_compiler     expressions -> stack machine, with a correctness proof
--                   and a verified constant-folding pass
--
-- Check with:  .lake/build/bin/mugda examples/showcase/sizedlib/sizedlib.ma

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

----------------------------------------------------------------------
-- Part 2: Algorithms that need sized types
--
-- Every function in this part terminates, but most are NOT structurally
-- recursive: the recursive argument is the result of a helper function
-- (minus, partition, split) or the application of a function stored in
-- a constructor (ordinals).  The size-change termination checker alone
-- cannot see that these arguments are smaller.  The size annotations
-- (`SNat i -> SNat # -> SNat i` says: the result is no bigger than the
-- first argument) give it exactly that information.
--
-- Note: we never use overlapping clauses.  The checker's evaluator does
-- not treat a stuck match as "blocked", so a catch-all clause would fire
-- on a neutral term during conversion checking (see README).
----------------------------------------------------------------------

-- Truncated subtraction, size preserving in its first argument.
fun sminus : (i : Size) -> SNat i -> SNat # -> SNat i
{
  sminus .($ i) (szero i)   y            = szero i;
  sminus .($ i) (ssucc i x) (szero .#)   = ssucc i x;
  sminus .($ i) (ssucc i x) (ssucc .# y) = sminus i x y
}

fun slt : (i : Size) -> SNat i -> (j : Size) -> SNat j -> Bool
{
  slt i x j y = leq (succ (toNat i x)) (toNat j y)
}

-- Floor division:  div x y = if x < y then 0 else 1 + div (x - y) y.
-- The recursive call is on `sminus i x y`, which is not a subterm of
-- `ssucc i x` -- it only has a smaller *size*.  Division by zero is 0.
fun sdiv : (i : Size) -> SNat i -> SNat # -> SNat i
{
  sdiv .($ i) (szero i)   y            = szero i;
  sdiv .($ i) (ssucc i x) (szero .#)   = szero i;
  sdiv .($ i) (ssucc i x) (ssucc .# y) =
    ite (SNat ($ i)) (slt i x # y)
        (szero i)
        (ssucc i (sdiv i (sminus i x y) (ssucc # y)))
}

-- Euclid's algorithm by repeated subtraction.  Each call shrinks one of
-- the two sizes and keeps the other: size-change termination combines
-- this with the size information from `sminus`.
fun sgcd : (i : Size) -> (j : Size) -> SNat i -> SNat j -> SNat #
{
  sgcd .($ i) j      (szero i)   y           = y;
  sgcd .($ i) .($ j) (ssucc i x) (szero j)   = ssucc i x;
  sgcd .($ i) .($ j) (ssucc i x) (ssucc j y) =
    ite (SNat #) (leq (toNat j y) (toNat i x))
        (sgcd i ($ j) (sminus i x y) (ssucc j y))
        (sgcd ($ i) j (ssucc i x) (sminus j y x))
}

let s7  : SNat # = fromNat n7
let s12 : SNat # = fromNat (add n6 n6)
let s18 : SNat # = fromNat (add n9 n9)

eval let div_7_2   : Dec = toDec (toNat # (sdiv # s7 (fromNat n2)))
eval let div_18_7  : Dec = toDec (toNat # (sdiv # s18 s7))
eval let gcd_12_18 : Dec = toDec (toNat # (sgcd # # s12 s18))

-- Ackermann's function: no sizes needed here, size-change termination
-- finds the lexicographic order (x, y) on its own.
fun ack : Nat -> Nat -> Nat
{
  ack zero     y        = succ y;
  ack (succ x) zero     = ack x n1;
  ack (succ x) (succ y) = ack x (ack (succ x) y)
}

eval let ack_2_3 : Dec = toDec (ack n2 n3)

----------------------------------------------------------------------
-- Quicksort.  `partition` returns two lists, each no longer than its
-- input.  The type `Prod (SList A i) (SList A i)` records this, so
-- both recursive calls of `qsapp` are on lists of size i < $ i.
----------------------------------------------------------------------

fun partition : (A : Set) -> (A -> Bool) -> (i : Size) -> SList A i ->
                Prod (SList A i) (SList A i)
{
  partition .A p .($ i) (snil A i) =
    pair (SList A ($ i)) (SList A ($ i)) (snil A i) (snil A i);
  partition .A p .($ i) (scons A i x xs) =
    let rec : Prod (SList A i) (SList A i) = partition A p i xs in
    let l1  : SList A i = fst (SList A i) (SList A i) rec in
    let l2  : SList A i = snd (SList A i) (SList A i) rec in
    ite (Prod (SList A ($ i)) (SList A ($ i))) (p x)
        (pair (SList A ($ i)) (SList A ($ i)) (scons A i x l1) l2)
        (pair (SList A ($ i)) (SList A ($ i)) l1 (scons A i x l2))
}

-- quicksort with an accumulator: qsapp xs acc = sort xs ++ acc
fun qsapp : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i ->
            SList A # -> SList A #
{
  qsapp .A le .($ i) (snil A i)       acc = acc;
  qsapp .A le .($ i) (scons A i x xs) acc =
    let pv    : Prod (SList A i) (SList A i) = partition A (\ y -> le y x) i xs in
    let small : SList A i = fst (SList A i) (SList A i) pv in
    let big   : SList A i = snd (SList A i) (SList A i) pv in
    qsapp A le i small (scons A # x (qsapp A le i big acc))
}

fun quicksort : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i -> SList A #
{
  quicksort A le i xs = qsapp A le i xs (snil A #)
}

eval let qs_digits : List Dec =
  decs (toList Nat # (quicksort Nat leq # (fromList Nat digits)))

----------------------------------------------------------------------
-- Merge sort.  `split` deals the elements out alternately into two
-- lists of size i, from a list of size $ $ i.  The recursive calls of
-- msort are then on lists of size $ i.
----------------------------------------------------------------------

fun split : (A : Set) -> (i : Size) -> SList A i -> Prod (SList A i) (SList A i)
{
  split .A .($ i) (snil A i) =
    pair (SList A ($ i)) (SList A ($ i)) (snil A i) (snil A i);
  split .A .($ ($ i)) (scons A .($ i) a (snil .A i)) =
    pair (SList A ($ ($ i))) (SList A ($ ($ i))) (scons A ($ i) a (snil A i)) (snil A i);
  split .A .($ ($ i)) (scons A .($ i) a (scons .A i b xs)) =
    let rec : Prod (SList A i) (SList A i) = split A i xs in
    let l1  : SList A i = fst (SList A i) (SList A i) rec in
    let l2  : SList A i = snd (SList A i) (SList A i) rec in
    pair (SList A ($ ($ i))) (SList A ($ ($ i))) (scons A ($ i) a l1) (scons A ($ i) b l2)
}

-- merge: lexicographic descent on the two lists.  (merge alone would also
-- pass without sizes; it is msort that needs them.)
fun merge : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i ->
            (j : Size) -> SList A j -> SList A #
{
  merge .A le .($ i) (snil A i)       j ys = ys;
  merge .A le .($ i) (scons A i x xs) .($ j) (snil .A j) = scons A i x xs;
  merge .A le .($ i) (scons A i x xs) .($ j) (scons .A j y ys) =
    ite (SList A #) (le x y)
        (scons A # x (merge A le i xs ($ j) (scons A j y ys)))
        (scons A # y (merge A le ($ i) (scons A i x xs) j ys))
}

fun msort : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i -> SList A #
{
  msort .A le .($ i) (snil A i) = snil A i;
  msort .A le .($ ($ i)) (scons A .($ i) a (snil .A i)) = scons A ($ i) a (snil A i);
  msort .A le .($ ($ i)) (scons A .($ i) a (scons .A i b xs)) =
    let sp : Prod (SList A i) (SList A i) = split A i xs in
    merge A le
      # (msort A le ($ i) (scons A i a (fst (SList A i) (SList A i) sp)))
      # (msort A le ($ i) (scons A i b (snd (SList A i) (SList A i) sp)))
}

eval let ms_digits : List Dec =
  decs (toList Nat # (msort Nat leq # (fromList Nat digits)))

----------------------------------------------------------------------
-- Rose trees: a node holds a label and a (sized) list of subtrees of
-- smaller size.  Recursion goes through `smap`, a higher-order function
-- that receives a partial application of the recursive call.  Without
-- the size index the checker cannot relate the elements of the child
-- list to the node.
----------------------------------------------------------------------

sized data Rose (+ A : Set) : Size -> Set
{
  rose : (i : Size) -> A -> SList (Rose A i) # -> Rose A ($ i)
}

fun mapRose : (A : Set) -> (B : Set) -> (A -> B) -> (i : Size) -> Rose A i -> Rose B i
{
  mapRose .A B f .($ i) (rose A i a ts) =
    rose B i (f a) (smap (Rose A i) (Rose B i) (mapRose A B f i) # ts)
}

fun sconcat : (A : Set) -> (i : Size) -> SList (SList A #) i -> SList A #
{
  sconcat A  .($ i) (snil .(SList A #) i)        = snil A #;
  sconcat A  .($ i) (scons .(SList A #) i l ls) = sappend A # l (sconcat A i ls)
}

-- pre-order flattening
fun flatten : (A : Set) -> (i : Size) -> Rose A i -> SList A #
{
  flatten .A .($ i) (rose A i a ts) =
    scons A # a (sconcat A # (smap (Rose A i) (SList A #) (flatten A i) # ts))
}

fun ssum : (i : Size) -> SList Nat i -> Nat
{
  ssum .($ i) (snil .Nat i)       = zero;
  ssum .($ i) (scons .Nat i x xs) = add x (ssum i xs)
}

-- number of nodes
fun sizeRose : (A : Set) -> (i : Size) -> Rose A i -> Nat
{
  sizeRose .A .($ i) (rose A i a ts) =
    succ (ssum # (smap (Rose A i) Nat (sizeRose A i) # ts))
}

let leafR : Nat -> Rose Nat # = \ n -> rose Nat # n (snil (Rose Nat #) #)

--        1
--      / | \
--     2  3  6
--       / \
--      4   5
let tree : Rose Nat # =
  rose Nat # n1
    (scons (Rose Nat #) # (leafR n2)
    (scons (Rose Nat #) # (rose Nat # n3
                             (scons (Rose Nat #) # (leafR n4)
                             (scons (Rose Nat #) # (leafR n5)
                             (snil (Rose Nat #) #))))
    (scons (Rose Nat #) # (leafR n6)
    (snil (Rose Nat #) #))))

eval let tree_flat : List Dec = decs (toList Nat # (flatten Nat # tree))
eval let tree_size : Dec = toDec (sizeRose Nat # tree)
eval let tree_doubled : List Dec =
  decs (toList Nat # (flatten Nat # (mapRose Nat Nat (\ n -> add n n) # tree)))

----------------------------------------------------------------------
-- Brouwer ordinals.  The limit constructor takes a whole sequence
-- `Nat -> Ord i`, so these trees are infinitely branching.  With sizes,
-- `f n : Ord i` is smaller than `olim i f : Ord ($ i)` by its type.
-- (The thesis needed an extra axiom "f n < olim f" for the unsized
-- version, examples/ord.ma.  The current checker's size-change order
-- already includes that rule, so here the sizes are for uniformity
-- rather than strictly necessary -- unlike div, gcd, the sorts and the
-- rose trees above, which are rejected without them; see bad/.)
----------------------------------------------------------------------

sized data Ord : Size -> Set
{
  ozero : (i : Size) -> Ord ($ i);
  osucc : (i : Size) -> Ord i -> Ord ($ i);
  olim  : (i : Size) -> (Nat -> Ord i) -> Ord ($ i)
}

fun ordOfNat : Nat -> Ord #
{
  ordOfNat zero     = ozero #;
  ordOfNat (succ n) = osucc # (ordOfNat n)
}

let omega : Ord # = olim # ordOfNat

-- ordinal addition, by recursion on the second argument
fun oadd : Ord # -> (i : Size) -> Ord i -> Ord #
{
  oadd x .($ i) (ozero i)   = x;
  oadd x .($ i) (osucc i y) = osucc # (oadd x i y);
  oadd x .($ i) (olim i f)  = olim # (\ n -> oadd x i (f n))
}

-- ordinal multiplication
fun omul : Ord # -> (i : Size) -> Ord i -> Ord #
{
  omul x .($ i) (ozero i)   = ozero #;
  omul x .($ i) (osucc i y) = oadd (omul x i y) # x;
  omul x .($ i) (olim i f)  = olim # (\ n -> omul x i (f n))
}

-- Follow the n-th branch at every limit and count the successors.
-- E.g. collapse (omega + omega) n = n + n.
fun collapse : (i : Size) -> Ord i -> Nat -> Nat
{
  collapse .($ i) (ozero i)   n = zero;
  collapse .($ i) (osucc i y) n = succ (collapse i y n);
  collapse .($ i) (olim i f)  n = collapse i (f n) n
}

eval let collapse_w_plus_w_3 : Dec = toDec (collapse # (oadd omega # omega) n3)
eval let collapse_w_times_3_2 : Dec = toDec (collapse # (omul omega # (ordOfNat n3)) n2)
eval let collapse_3_times_w_2 : Dec = toDec (collapse # (omul (ordOfNat n3) # omega) n2)

----------------------------------------------------------------------
-- Part 3: Coinduction -- sized streams, stream processors, bisimulation
--
-- A `cofun` must be productive: each corecursive call has to be at a
-- smaller size, which can only happen under a constructor (`stcons i x
-- (f i ...)` has size $ i).  Mugda's admissibility rules allow sized
-- coinductive *results* `Stream A i`, but inputs must be at size `#`.
-- (A cofun that consumes `Stream A i` is rejected as "type not
-- admissible".)  So everything here takes `Stream A #` arguments.
----------------------------------------------------------------------

sized codata Stream (+ A : Set) : Size -> Set
{
  stcons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

fun head : (A : Set) -> Stream A # -> A
{
  head .A (stcons A .# x xs) = x
}

fun tail : (A : Set) -> Stream A # -> Stream A #
{
  tail .A (stcons A .# x xs) = xs
}

fun nth : (A : Set) -> Nat -> Stream A # -> A
{
  nth A zero     s = head A s;
  nth A (succ n) s = nth A n (tail A s)
}

-- the first n elements
fun take : (A : Set) -> Nat -> Stream A # -> List A
{
  take A zero     s = nil A;
  take A (succ n) s = cons A (head A s) (take A n (tail A s))
}

cofun repeat : (A : Set) -> (i : Size) -> A -> Stream A i
{
  repeat A ($ i) x = stcons A i x (repeat A i x)
}

cofun iterate : (A : Set) -> (A -> A) -> (i : Size) -> A -> Stream A i
{
  iterate A f ($ i) x = stcons A i x (iterate A f i (f x))
}

cofun nats : (i : Size) -> Nat -> Stream Nat i
{
  nats ($ i) n = stcons Nat i n (nats i (succ n))
}

-- Fibonacci numbers, generated from the state (x, y)
cofun fibFrom : Nat -> Nat -> (i : Size) -> Stream Nat i
{
  fibFrom x y ($ i) = stcons Nat i x (fibFrom y (add x y) i)
}

let fibs : Stream Nat # = fibFrom n0 n1 #

cofun stmap : (A : Set) -> (B : Set) -> (A -> B) -> (i : Size) -> Stream A # -> Stream B i
{
  stmap .A B f ($ i) (stcons A .# x xs) = stcons B i (f x) (stmap A B f i xs)
}

cofun zipWith : (A : Set) -> (B : Set) -> (C : Set) -> (A -> B -> C) -> (i : Size) ->
                Stream A # -> Stream B # -> Stream C i
{
  zipWith .A .B C f ($ i) (stcons A .# a as) (stcons B .# b bs) =
    stcons C i (f a b) (zipWith A B C f i as bs)
}

-- interleave swaps its arguments on each step
cofun interleave : (A : Set) -> (i : Size) -> Stream A # -> Stream A # -> Stream A i
{
  interleave .A ($ i) (stcons A .# x xs) t = stcons A i x (interleave A i t xs)
}

-- every second element: productive although it drops elements, because
-- one output is produced per corecursive call
cofun evens : (A : Set) -> (i : Size) -> Stream A # -> Stream A i
{
  evens .A ($ i) (stcons A .# x xs) = stcons A i x (evens A i (tail A xs))
}

-- Merge two ascending streams and drop duplicates (Hamming style).
-- Each step emits exactly one element.
cofun umerge : (i : Size) -> Stream Nat # -> Stream Nat # -> Stream Nat i
{
  umerge ($ i) (stcons .Nat .# x xs) (stcons .Nat .# y ys) =
    ite (Stream Nat ($ i)) (leq x y)
        (ite (Stream Nat ($ i)) (leq y x)
             (stcons Nat i x (umerge i xs ys))
             (stcons Nat i x (umerge i xs (stcons Nat # y ys))))
        (stcons Nat i y (umerge i (stcons Nat # x xs) ys))
}

let positives : Stream Nat # = nats # n1

-- numbers divisible by 2 or by 3: 2,3,4,6,8,9,10,12,...
let mult23 : Stream Nat # =
  umerge # (stmap Nat Nat (mul n2) # positives) (stmap Nat Nat (mul n3) # positives)

eval let fib_first8   : List Dec = decs (take Nat n8 fibs)
eval let fib_8        : Dec      = toDec (nth Nat n8 fibs)
eval let mult23_first8 : List Dec = decs (take Nat n8 mult23)
eval let fib_plus_nats : List Dec = decs (take Nat n5 (zipWith Nat Nat Nat add # fibs (nats # n0)))
eval let interleaved  : List Dec = decs (take Nat n6 (interleave Nat # (repeat Nat # n0) (repeat Nat # n1)))
eval let evens_nats   : List Dec = decs (take Nat n5 (evens Nat # (nats # n0)))

----------------------------------------------------------------------
-- Stream processors (after examples/sp.ma).  An `ISP K` is a finite
-- (inductive) tree of `get` requests that ends in a `put` of one output
-- value, followed by the continuation K.  A stream processor `SP` is the
-- coinductive tie of the knot: K = SP again.  Because the ISP part is
-- inductive, a processor can only read finitely many inputs before it
-- must produce an output -- so `eat` is productive.  (A `filter` that
-- may skip infinitely many inputs cannot be written as an SP.)
----------------------------------------------------------------------

data ISP (+ K : Set) : Set
{
  put : Nat -> K -> ISP K;
  get : (Nat -> ISP K) -> ISP K
}

sized codata SP : Size -> Set
{
  isp : (i : Size) -> ISP (SP i) -> SP ($ i)
}

-- run the inductive part, then hand output, continuation and the rest of
-- the input to h
fun ieat : (K : Set) -> (C : Set) -> ISP K -> Stream Nat # ->
           (Nat -> K -> Stream Nat # -> C) -> C
{
  ieat .K C (get K f)   (stcons .Nat .# a as) h = ieat K C (f a) as h;
  ieat .K C (put K b k) as                    h = h b k as
}

cofun eat : (i : Size) -> SP # -> Stream Nat # -> Stream Nat i
{
  eat ($ i) (isp .# ip) as =
    ieat (SP #) (Stream Nat ($ i)) ip as
         (\ b -> \ k -> \ as' -> stcons Nat i b (eat i k as'))
}

-- read two numbers, output their sum, repeat
cofun pairSums : (i : Size) -> SP i
{
  pairSums ($ i) =
    isp i (get (SP i) (\ x -> get (SP i) (\ y -> put (SP i) (add x y) (pairSums i))))
}

-- running total, the state is the accumulator
cofun runSum : (i : Size) -> Nat -> SP i
{
  runSum ($ i) acc =
    isp i (get (SP i) (\ x -> put (SP i) (add acc x) (runSum i (add acc x))))
}

-- read n, then add up the next n numbers (examples/sp.ma)
fun iadder : Nat -> Nat -> (K : Set) -> K -> ISP K
{
  iadder zero     acc K k = put K acc k;
  iadder (succ n) acc K k = get K (\ m -> iadder n (add m acc) K k)
}

cofun adder : (i : Size) -> SP i
{
  adder ($ i) = isp i (get (SP i) (\ n -> iadder n zero (SP i) (adder i)))
}

eval let sp_pairsums : List Dec = decs (take Nat n4 (eat # (pairSums #) (nats # n0)))
eval let sp_runsum   : List Dec = decs (take Nat n5 (eat # (runSum # n0) positives))
eval let sp_adder    : List Dec = decs (take Nat n3 (eat # (adder #) (repeat Nat # n2)))

----------------------------------------------------------------------
-- Bisimulation.  `Bisim A i s t` is a sized coinductive relation: s and t
-- agree on their first i elements; at size # they are bisimilar.
-- Proofs are cofuns.  Checking them needs the type checker to unfold
-- cofuns (e.g. `nats # n` to `stcons Nat # n (nats # (succ n))`).
----------------------------------------------------------------------

sized codata Bisim (A : Set) : Size -> Stream A # -> Stream A # -> Set
{
  bisim : (i : Size) -> (x : A) -> (s : Stream A #) -> (t : Stream A #) ->
          Bisim A i s t -> Bisim A ($ i) (stcons A # x s) (stcons A # x t)
}

cofun bisim_refl : (A : Set) -> (i : Size) -> (s : Stream A #) -> Bisim A i s s
{
  bisim_refl .A ($ i) (stcons A .# x xs) = bisim A i x xs xs (bisim_refl A i xs)
}

-- map f (iterate f x)  ~  iterate f (f x)
cofun map_iterate : (A : Set) -> (f : A -> A) -> (i : Size) -> (x : A) ->
  Bisim A i (stmap A A f # (iterate A f # x)) (iterate A f # (f x))
{
  map_iterate A f ($ i) x =
    bisim A i (f x) (stmap A A f # (iterate A f # (f x))) (iterate A f # (f (f x)))
          (map_iterate A f i (f x))
}

-- nats n  ~  iterate succ n
cofun nats_iterate : (i : Size) -> (n : Nat) ->
  Bisim Nat i (nats # n) (iterate Nat succ # n)
{
  nats_iterate ($ i) n =
    bisim Nat i n (nats # (succ n)) (iterate Nat succ # (succ n)) (nats_iterate i (succ n))
}

-- map succ (nats n)  ~  nats (succ n)
cofun map_succ_nats : (i : Size) -> (n : Nat) ->
  Bisim Nat i (stmap Nat Nat succ # (nats # n)) (nats # (succ n))
{
  map_succ_nats ($ i) n =
    bisim Nat i (succ n) (stmap Nat Nat succ # (nats # (succ n))) (nats # (succ (succ n)))
          (map_succ_nats i (succ n))
}

-- Bisimilar streams have equal prefixes (an inductive consequence of a
-- coinductive proof): the first n elements agree.
fun bisim_take : (A : Set) -> (n : Nat) -> (s : Stream A #) -> (t : Stream A #) ->
                 Bisim A # s t -> Eq (List A) (take A n s) (take A n t)
{
  bisim_take A zero     s t p = refl (List A) (nil A);
  bisim_take A (succ n) .(stcons A # x s') .(stcons A # x t') (bisim .A .# x s' t' p) =
    cong (List A) (List A) (cons A x) (take A n s') (take A n t') (bisim_take A n s' t' p)
}

eval let prefix_eq : Eq (List Nat) (take Nat n3 (nats # n0)) (take Nat n3 (iterate Nat succ # n0)) =
  bisim_take Nat n3 (nats # n0) (iterate Nat succ # n0) (nats_iterate # n0)

----------------------------------------------------------------------
-- Part 4: A verified compiler
--
-- Source:  arithmetic expressions with constants, +, * and if-zero.
-- Target:  a stack machine.  Code is a list of instructions; the
--          if-zero instruction carries its two branches as nested code
--          (structured control flow instead of jumps).
--
-- Theorem (compile_correct):
--   exec (compile e ++ c) s  ==  exec c (evalE e :: s)
--
-- Everything is proved in full -- nothing had to be dropped.  Two design
-- choices make this possible in Mugda:
--   * Structured branches (`ibranch then else`) instead of jump offsets.
--     With jumps, exec would need fuel or well-founded recursion, and the
--     proof would need arithmetic on code addresses.
--   * `exec (i :: c) s = exec c (step i s)`.  This makes the key lemma
--     exec (c1 ++ c2) s = exec c2 (exec c1 s) a one-line induction that
--     never inspects the instruction.
-- Stack underflow is not ruled out by types (we use an untyped stack and
-- let a binary operation on a too-short stack leave it unchanged); the
-- theorem shows that compiled code never underflows.
--
-- The termination checker accepts all of this structurally (no sizes
-- needed): exec and step are mutually recursive and the nested code of
-- `ibranch t e` is a subterm of the instruction list.
----------------------------------------------------------------------

data Expr : Set
{
  lit   : Nat -> Expr;
  plus  : Expr -> Expr -> Expr;
  times : Expr -> Expr -> Expr;
  ifz   : Expr -> Expr -> Expr -> Expr      -- if-zero c then t else e
}

fun ifzero : (A : Set) -> Nat -> A -> A -> A
{
  ifzero A zero     a b = a;
  ifzero A (succ n) a b = b
}

-- the denotational semantics
fun evalE : Expr -> Nat
{
  evalE (lit n)     = n;
  evalE (plus a b)  = add (evalE a) (evalE b);
  evalE (times a b) = mul (evalE a) (evalE b);
  evalE (ifz c t e) = ifzero Nat (evalE c) (evalE t) (evalE e)
}

data Instr : Set
{
  ipush   : Nat -> Instr;
  iadd    : Instr;
  imul    : Instr;
  ibranch : List Instr -> List Instr -> Instr  -- pop n; run first code if n = 0
}

let Code  : Set = List Instr
let Stack : Set = List Nat

-- pop y, pop x, push (f x y)
fun binop : (Nat -> Nat -> Nat) -> Stack -> Stack
{
  binop f (nil .Nat)                    = nil Nat;
  binop f (cons .Nat y (nil .Nat))      = cons Nat y (nil Nat);
  binop f (cons .Nat y (cons .Nat x s)) = cons Nat (f x y) s
}

-- pop n, then continue with f (n = 0) or g (n > 0)
fun branch : (Stack -> Stack) -> (Stack -> Stack) -> Stack -> Stack
{
  branch f g (nil .Nat)             = nil Nat;
  branch f g (cons .Nat zero s)     = f s;
  branch f g (cons .Nat (succ n) s) = g s
}

mutual
{
  fun exec : Code -> Stack -> Stack
  {
    exec (nil .Instr)      s = s;
    exec (cons .Instr i c) s = exec c (step i s)
  }

  fun step : Instr -> Stack -> Stack
  {
    step (ipush n)     s = cons Nat n s;
    step iadd          s = binop add s;
    step imul          s = binop mul s;
    step (ibranch t e) s = branch (exec t) (exec e) s
  }
}

let single : Instr -> Code = \ i -> cons Instr i (nil Instr)

fun compile : Expr -> Code
{
  compile (lit n)     = single (ipush n);
  compile (plus a b)  = append Instr (compile a) (append Instr (compile b) (single iadd));
  compile (times a b) = append Instr (compile a) (append Instr (compile b) (single imul));
  compile (ifz c t e) = append Instr (compile c) (single (ibranch (compile t) (compile e)))
}

----------------------------------------------------------------------
-- Correctness proof
----------------------------------------------------------------------

-- Running concatenated code = running the parts one after the other.
fun exec_append : (c1 : Code) -> (c2 : Code) -> (s : Stack) ->
  Eq Stack (exec (append Instr c1 c2) s) (exec c2 (exec c1 s))
{
  exec_append (nil .Instr)      c2 s = refl Stack (exec c2 s);
  exec_append (cons .Instr i c1) c2 s = exec_append c1 c2 (step i s)
}

-- Two sub-computations in sequence, followed by code k.  Used for both
-- binary operators.
fun seq2 : (ca : Code) -> (cb : Code) -> (k : Code) -> (va : Nat) -> (vb : Nat) ->
  (s : Stack) ->
  Eq Stack (exec ca s) (cons Nat va s) ->
  Eq Stack (exec cb (cons Nat va s)) (cons Nat vb (cons Nat va s)) ->
  Eq Stack (exec (append Instr ca (append Instr cb k)) s)
           (exec k (cons Nat vb (cons Nat va s)))
{
  seq2 ca cb k va vb s pa pb =
    trans Stack
      (exec (append Instr ca (append Instr cb k)) s)
      (exec (append Instr cb k) (exec ca s))
      (exec k (cons Nat vb (cons Nat va s)))
      (exec_append ca (append Instr cb k) s)
      (trans Stack
        (exec (append Instr cb k) (exec ca s))
        (exec (append Instr cb k) (cons Nat va s))
        (exec k (cons Nat vb (cons Nat va s)))
        (cong Stack Stack (exec (append Instr cb k)) (exec ca s) (cons Nat va s) pa)
        (trans Stack
          (exec (append Instr cb k) (cons Nat va s))
          (exec k (exec cb (cons Nat va s)))
          (exec k (cons Nat vb (cons Nat va s)))
          (exec_append cb k (cons Nat va s))
          (cong Stack Stack (exec k) (exec cb (cons Nat va s))
                (cons Nat vb (cons Nat va s)) pb)))
}

-- The branch instruction does the right thing, by case analysis on the
-- popped value.  (Mugda has no `with`; the case split is a helper
-- function that matches on n.)
fun branch_ok : (ct : Code) -> (ce : Code) -> (vt : Nat) -> (ve : Nat) -> (s : Stack) ->
  Eq Stack (exec ct s) (cons Nat vt s) ->
  Eq Stack (exec ce s) (cons Nat ve s) ->
  (n : Nat) ->
  Eq Stack (branch (exec ct) (exec ce) (cons Nat n s)) (cons Nat (ifzero Nat n vt ve) s)
{
  branch_ok ct ce vt ve s pt pe zero     = pt;
  branch_ok ct ce vt ve s pt pe (succ n) = pe
}

-- Compiled code pushes the value of the expression.
fun correct : (e : Expr) -> (s : Stack) ->
  Eq Stack (exec (compile e) s) (cons Nat (evalE e) s)
{
  correct (lit n) s = refl Stack (cons Nat n s);
  correct (plus a b) s =
    seq2 (compile a) (compile b) (single iadd) (evalE a) (evalE b) s
         (correct a s) (correct b (cons Nat (evalE a) s));
  correct (times a b) s =
    seq2 (compile a) (compile b) (single imul) (evalE a) (evalE b) s
         (correct a s) (correct b (cons Nat (evalE a) s));
  correct (ifz c t e) s =
    let k : Code = single (ibranch (compile t) (compile e)) in
    trans Stack
      (exec (append Instr (compile c) k) s)
      (exec k (exec (compile c) s))
      (cons Nat (ifzero Nat (evalE c) (evalE t) (evalE e)) s)
      (exec_append (compile c) k s)
      (trans Stack
        (exec k (exec (compile c) s))
        (exec k (cons Nat (evalE c) s))
        (cons Nat (ifzero Nat (evalE c) (evalE t) (evalE e)) s)
        (cong Stack Stack (exec k) (exec (compile c) s) (cons Nat (evalE c) s) (correct c s))
        (branch_ok (compile t) (compile e) (evalE t) (evalE e) s
                   (correct t s) (correct e s) (evalE c)))
}

-- The main theorem: exec (compile e ++ c) s == exec c (evalE e :: s)
fun compile_correct : (e : Expr) -> (c : Code) -> (s : Stack) ->
  Eq Stack (exec (append Instr (compile e) c) s) (exec c (cons Nat (evalE e) s))
{
  compile_correct e c s =
    trans Stack
      (exec (append Instr (compile e) c) s)
      (exec c (exec (compile e) s))
      (exec c (cons Nat (evalE e) s))
      (exec_append (compile e) c s)
      (cong Stack Stack (exec c) (exec (compile e) s) (cons Nat (evalE e) s) (correct e s))
}

----------------------------------------------------------------------
-- A verified optimisation pass: constant folding.
-- To avoid overlapping clauses (see Part 2), the "smart constructors"
-- match on every constructor of the first argument.
----------------------------------------------------------------------

fun foldPlus : Expr -> Expr -> Expr
{
  foldPlus (lit n)     (lit m)     = lit (add n m);
  foldPlus (lit n)     (plus c d)  = plus (lit n) (plus c d);
  foldPlus (lit n)     (times c d) = plus (lit n) (times c d);
  foldPlus (lit n)     (ifz c d f) = plus (lit n) (ifz c d f);
  foldPlus (plus a b)  y           = plus (plus a b) y;
  foldPlus (times a b) y           = plus (times a b) y;
  foldPlus (ifz a b c) y           = plus (ifz a b c) y
}

fun foldTimes : Expr -> Expr -> Expr
{
  foldTimes (lit n)     (lit m)     = lit (mul n m);
  foldTimes (lit n)     (plus c d)  = times (lit n) (plus c d);
  foldTimes (lit n)     (times c d) = times (lit n) (times c d);
  foldTimes (lit n)     (ifz c d f) = times (lit n) (ifz c d f);
  foldTimes (plus a b)  y           = times (plus a b) y;
  foldTimes (times a b) y           = times (times a b) y;
  foldTimes (ifz a b c) y           = times (ifz a b c) y
}

-- if-zero with a known condition picks its branch at compile time
fun foldIfz : Expr -> Expr -> Expr -> Expr
{
  foldIfz (lit zero)     t e = t;
  foldIfz (lit (succ n)) t e = e;
  foldIfz (plus a b)     t e = ifz (plus a b) t e;
  foldIfz (times a b)    t e = ifz (times a b) t e;
  foldIfz (ifz a b c)    t e = ifz (ifz a b c) t e
}

fun cfold : Expr -> Expr
{
  cfold (lit n)     = lit n;
  cfold (plus a b)  = foldPlus (cfold a) (cfold b);
  cfold (times a b) = foldTimes (cfold a) (cfold b);
  cfold (ifz c t e) = foldIfz (cfold c) (cfold t) (cfold e)
}

-- Each smart constructor is correct, by computation in every case.
fun foldPlus_ok : (x : Expr) -> (y : Expr) ->
  Eq Nat (evalE (foldPlus x y)) (add (evalE x) (evalE y))
{
  foldPlus_ok (lit n)     (lit m)     = refl Nat (add n m);
  foldPlus_ok (lit n)     (plus c d)  = refl Nat (add n (add (evalE c) (evalE d)));
  foldPlus_ok (lit n)     (times c d) = refl Nat (add n (mul (evalE c) (evalE d)));
  foldPlus_ok (lit n)     (ifz c d f) = refl Nat (add n (evalE (ifz c d f)));
  foldPlus_ok (plus a b)  y           = refl Nat (add (evalE (plus a b)) (evalE y));
  foldPlus_ok (times a b) y           = refl Nat (add (evalE (times a b)) (evalE y));
  foldPlus_ok (ifz a b c) y           = refl Nat (add (evalE (ifz a b c)) (evalE y))
}

fun foldTimes_ok : (x : Expr) -> (y : Expr) ->
  Eq Nat (evalE (foldTimes x y)) (mul (evalE x) (evalE y))
{
  foldTimes_ok (lit n)     (lit m)     = refl Nat (mul n m);
  foldTimes_ok (lit n)     (plus c d)  = refl Nat (mul n (add (evalE c) (evalE d)));
  foldTimes_ok (lit n)     (times c d) = refl Nat (mul n (mul (evalE c) (evalE d)));
  foldTimes_ok (lit n)     (ifz c d f) = refl Nat (mul n (evalE (ifz c d f)));
  foldTimes_ok (plus a b)  y           = refl Nat (mul (evalE (plus a b)) (evalE y));
  foldTimes_ok (times a b) y           = refl Nat (mul (evalE (times a b)) (evalE y));
  foldTimes_ok (ifz a b c) y           = refl Nat (mul (evalE (ifz a b c)) (evalE y))
}

fun foldIfz_ok : (c : Expr) -> (t : Expr) -> (e : Expr) ->
  Eq Nat (evalE (foldIfz c t e)) (ifzero Nat (evalE c) (evalE t) (evalE e))
{
  foldIfz_ok (lit zero)     t e = refl Nat (evalE t);
  foldIfz_ok (lit (succ n)) t e = refl Nat (evalE e);
  foldIfz_ok (plus a b)     t e = refl Nat (evalE (ifz (plus a b) t e));
  foldIfz_ok (times a b)    t e = refl Nat (evalE (ifz (times a b) t e));
  foldIfz_ok (ifz a b c)    t e = refl Nat (evalE (ifz (ifz a b c) t e))
}

-- congruence for two and three arguments
fun cong2 : (A : Set) -> (B : Set) -> (C : Set) -> (f : A -> B -> C) ->
  (a : A) -> (a' : A) -> (b : B) -> (b' : B) ->
  Eq A a a' -> Eq B b b' -> Eq C (f a b) (f a' b')
{
  cong2 .A .B C f .a .a .b .b (refl A a) (refl B b) = refl C (f a b)
}

fun cong3 : (A : Set) -> (B : Set) -> (C : Set) -> (D : Set) -> (f : A -> B -> C -> D) ->
  (a : A) -> (a' : A) -> (b : B) -> (b' : B) -> (c : C) -> (c' : C) ->
  Eq A a a' -> Eq B b b' -> Eq C c c' -> Eq D (f a b c) (f a' b' c')
{
  cong3 .A .B .C D f .a .a .b .b .c .c (refl A a) (refl B b) (refl C c) = refl D (f a b c)
}

-- constant folding preserves the meaning of every expression
fun cfold_ok : (e : Expr) -> Eq Nat (evalE (cfold e)) (evalE e)
{
  cfold_ok (lit n) = refl Nat n;
  cfold_ok (plus a b) =
    trans Nat (evalE (foldPlus (cfold a) (cfold b)))
              (add (evalE (cfold a)) (evalE (cfold b)))
              (add (evalE a) (evalE b))
      (foldPlus_ok (cfold a) (cfold b))
      (cong2 Nat Nat Nat add (evalE (cfold a)) (evalE a) (evalE (cfold b)) (evalE b)
             (cfold_ok a) (cfold_ok b));
  cfold_ok (times a b) =
    trans Nat (evalE (foldTimes (cfold a) (cfold b)))
              (mul (evalE (cfold a)) (evalE (cfold b)))
              (mul (evalE a) (evalE b))
      (foldTimes_ok (cfold a) (cfold b))
      (cong2 Nat Nat Nat mul (evalE (cfold a)) (evalE a) (evalE (cfold b)) (evalE b)
             (cfold_ok a) (cfold_ok b));
  cfold_ok (ifz c t e) =
    trans Nat (evalE (foldIfz (cfold c) (cfold t) (cfold e)))
              (ifzero Nat (evalE (cfold c)) (evalE (cfold t)) (evalE (cfold e)))
              (ifzero Nat (evalE c) (evalE t) (evalE e))
      (foldIfz_ok (cfold c) (cfold t) (cfold e))
      (cong3 Nat Nat Nat Nat (ifzero Nat)
             (evalE (cfold c)) (evalE c) (evalE (cfold t)) (evalE t)
             (evalE (cfold e)) (evalE e)
             (cfold_ok c) (cfold_ok t) (cfold_ok e))
}

-- The optimising compiler is correct, too.
fun optimised_correct : (e : Expr) -> (s : Stack) ->
  Eq Stack (exec (compile (cfold e)) s) (cons Nat (evalE e) s)
{
  optimised_correct e s =
    trans Stack
      (exec (compile (cfold e)) s)
      (cons Nat (evalE (cfold e)) s)
      (cons Nat (evalE e) s)
      (correct (cfold e) s)
      (cong Nat Stack (\ v -> cons Nat v s) (evalE (cfold e)) (evalE e) (cfold_ok e))
}

----------------------------------------------------------------------
-- Running the compiler
----------------------------------------------------------------------

-- (2 + 3) * (if-zero (1 * 0) then 4 else 9)  =  5 * 4  =  20
let prog : Expr =
  times (plus (lit n2) (lit n3))
        (ifz (times (lit n1) (lit n0)) (lit n4) (lit n9))

let empty : Stack = nil Nat

eval let prog_value    : Dec       = toDec (evalE prog)
eval let prog_code     : Code      = compile prog
eval let prog_run      : List Dec  = decs (exec (compile prog) empty)
eval let prog_folded   : Expr      = cfold prog
eval let prog_opt_code : Code      = compile (cfold prog)

-- instances of the theorems; a proof of a closed equation normalises to refl
eval let prog_ok : Eq Stack (exec (compile prog) empty) (cons Nat (evalE prog) empty)
  = correct prog empty
eval let prog_opt_ok : Eq Stack (exec (compile (cfold prog)) empty) (cons Nat (evalE prog) empty)
  = optimised_correct prog empty
