-- Showcase 2: Coinductive Stream Bisimulation & Stream Fusion Proofs
-- Expect: accept
--
-- A self-contained coinductive verification showcase in Mugda:
--   1. Infinite streams (`sized codata Stream`) and corecursive combinators
--      (`repeat`, `map`, `zipWith`, `iterate`, `interleave`, `evens`, `odds`).
--   2. Sized coinductive stream bisimulation (`sized codata Bisim`):
--      two streams `s1, s2 : Stream A #` are bisimilar to depth `i` (`Bisim A i s1 s2`)
--      when their heads agree and their tails are bisimilar to depth `i - 1`.
--   3. Equivalence relation proofs by productive corecursion (`cofun`):
--      - `bisimRefl`  : reflexivity  (`s ~ s`)
--      - `bisimSymm`  : symmetry     (`s1 ~ s2 -> s2 ~ s1`)
--      - `bisimTrans` : transitivity (`s1 ~ s2 -> s2 ~ s3 -> s1 ~ s3`)
--   4. Coinductive stream law & fusion proofs:
--      - `bisimMapCong`     : `s1 ~ s2 -> map f s1 ~ map f s2`
--      - `bisimMapId`       : `map (\x -> x) s ~ s`
--      - `bisimMapFusion`   : `map g (map f s) ~ map (\x -> g (f x)) s`
--      - `bisimMapRepeat`   : `map f (repeat a) ~ repeat (f a)`
--      - `bisimIterateMap`  : `iterate f (f a) ~ map f (iterate f a)`
--      - `bisimInterleave`  : `interleave (evens s) (odds s) ~ s`
--   5. Inductive projection & observation soundness (`fun`):
--      - `bisimHead`   : `s1 ~ s2 -> Eq A (head s1) (head s2)`
--      - `bisimTail`   : `s1 ~ s2 -> tail s1 ~ tail s2`
--      - `bisimNthEq`  : `s1 ~ s2 -> (n : Nat) -> Eq A (nth n s1) (nth n s2)`
--      - `bisimTakeEq` : `s1 ~ s2 -> (n : Nat) -> Eq (List A) (take n s1) (take n s2)`

------------------------------------------------------------------------
-- 1. Basic Data Types & Propositional Equality
------------------------------------------------------------------------

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

fun add : Nat -> Nat -> Nat
{
  add zero     y = y;
  add (succ x) y = succ (add x y)
}

fun double : Nat -> Nat
{
  double zero     = zero;
  double (succ n) = succ (succ (double n))
}

data List (+ A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

data Eq (A : Set) : A -> A -> Set
{
  refl : (a : A) -> Eq A a a
}

fun congCons : (A : Set) -> (x : A) -> (xs : List A) -> (ys : List A) ->
               Eq (List A) xs ys -> Eq (List A) (cons A x xs) (cons A x ys)
{
  congCons A x .xs .xs (refl .(List A) xs) = refl (List A) (cons A x xs)
}

------------------------------------------------------------------------
-- 2. Sized Coinductive Streams & Combinators
------------------------------------------------------------------------

sized codata Stream (+ A : Set) : Size -> Set
{
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

fun head : (A : Set) -> Stream A # -> A
{
  head .A (scons A .# x xs) = x
}

fun tail : (A : Set) -> Stream A # -> Stream A #
{
  tail .A (scons A .# x xs) = xs
}

fun nth : (A : Set) -> Nat -> Stream A # -> A
{
  nth A zero     s = head A s;
  nth A (succ n) s = nth A n (tail A s)
}

fun take : (A : Set) -> Nat -> Stream A # -> List A
{
  take A zero     s = nil A;
  take A (succ n) s = cons A (head A s) (take A n (tail A s))
}

cofun repeat : (A : Set) -> A -> (i : Size) -> Stream A i
{
  repeat A a ($ i) = scons A i a (repeat A a i)
}

cofun from : Nat -> (i : Size) -> Stream Nat i
{
  from n ($ i) = scons Nat i n (from (succ n) i)
}

cofun iterate : (A : Set) -> (A -> A) -> A -> (i : Size) -> Stream A i
{
  iterate A f a ($ i) = scons A i a (iterate A f (f a) i)
}

cofun map : (A : Set) -> (B : Set) -> (A -> B) -> Stream A # -> (i : Size) -> Stream B i
{
  map .A B f (scons A .# x xs) ($ i) = scons B i (f x) (map A B f xs i)
}

cofun interleave : (A : Set) -> Stream A # -> Stream A # -> (i : Size) -> Stream A i
{
  interleave .A (scons A .# x xs) ys ($ i) = scons A i x (interleave A ys xs i)
}

cofun evens : (A : Set) -> Stream A # -> (i : Size) -> Stream A i
{
  evens .A (scons A .# x (scons .A .# y xs)) ($ i) = scons A i x (evens A xs i)
}

cofun odds : (A : Set) -> Stream A # -> (i : Size) -> Stream A i
{
  odds .A (scons A .# x (scons .A .# y xs)) ($ i) = scons A i y (odds A xs i)
}

------------------------------------------------------------------------
-- 3. Sized Coinductive Bisimulation (`Bisim`)
------------------------------------------------------------------------

sized codata Bisim (+ A : Set) : Size -> Stream A # -> Stream A # -> Set
{
  bisimCons : (i : Size) -> (x : A) -> (xs : Stream A #) -> (ys : Stream A #) ->
              Bisim A i xs ys ->
              Bisim A ($ i) (scons A # x xs) (scons A # x ys)
}

-- Destructors on Bisim at limit size #
fun bisimHead : (A : Set) -> (s1 : Stream A #) -> (s2 : Stream A #) ->
                Bisim A # s1 s2 -> Eq A (head A s1) (head A s2)
{
  bisimHead .A .(scons A # x xs) .(scons A # x ys) (bisimCons A .# x xs ys b) =
    refl A x
}

fun bisimTail : (A : Set) -> (s1 : Stream A #) -> (s2 : Stream A #) ->
                Bisim A # s1 s2 -> Bisim A # (tail A s1) (tail A s2)
{
  bisimTail .A .(scons A # x xs) .(scons A # x ys) (bisimCons A .# x xs ys b) =
    b
}

-- Bisimilarity implies propositional equality of n-th elements for all n : Nat
fun bisimNthEq : (A : Set) -> (n : Nat) -> (s1 : Stream A #) -> (s2 : Stream A #) ->
                 Bisim A # s1 s2 -> Eq A (nth A n s1) (nth A n s2)
{
  bisimNthEq A zero     s1 s2 b = bisimHead A s1 s2 b;
  bisimNthEq A (succ n) s1 s2 b = bisimNthEq A n (tail A s1) (tail A s2) (bisimTail A s1 s2 b)
}

-- Bisimilarity implies propositional equality of all finite prefixes `take A n`
fun bisimTakeEq : (A : Set) -> (n : Nat) -> (s1 : Stream A #) -> (s2 : Stream A #) ->
                  Bisim A # s1 s2 -> Eq (List A) (take A n s1) (take A n s2)
{
  bisimTakeEq A zero     s1 s2 b = refl (List A) (nil A);
  bisimTakeEq .A (succ n) .(scons A # x xs) .(scons A # x ys) (bisimCons A .# x xs ys b) =
    congCons A x (take A n xs) (take A n ys) (bisimTakeEq A n xs ys b)
}

------------------------------------------------------------------------
-- 4. Equivalence Relation Proofs (`bisimRefl`, `bisimSymm`, `bisimTrans`)
------------------------------------------------------------------------

cofun bisimRefl : (A : Set) -> (s : Stream A #) -> (i : Size) -> Bisim A i s s
{
  bisimRefl .A (scons A .# x xs) ($ i) =
    bisimCons A i x xs xs (bisimRefl A xs i)
}

cofun bisimSymm : (A : Set) -> (s1 : Stream A #) -> (s2 : Stream A #) ->
                  Bisim A # s1 s2 -> (i : Size) -> Bisim A i s2 s1
{
  bisimSymm .A .(scons A # x xs) .(scons A # x ys) (bisimCons A .# x xs ys b) ($ i) =
    bisimCons A i x ys xs (bisimSymm A xs ys b i)
}

cofun bisimTrans : (A : Set) -> (s1 : Stream A #) -> (s2 : Stream A #) -> (s3 : Stream A #) ->
                   Bisim A # s1 s2 -> Bisim A # s2 s3 -> (i : Size) -> Bisim A i s1 s3
{
  bisimTrans .A .(scons A # x xs) .(scons A # x ys) .(scons A # x zs)
             (bisimCons A .# x xs ys b1) (bisimCons .A .# .x .ys zs b2) ($ i) =
    bisimCons A i x xs zs (bisimTrans A xs ys zs b1 b2 i)
}

------------------------------------------------------------------------
-- 5. Coinductive Stream Law & Fusion Proofs
------------------------------------------------------------------------

-- Congruence of `map` under bisimulation
cofun bisimMapCong : (A : Set) -> (B : Set) -> (f : A -> B) ->
                     (s1 : Stream A #) -> (s2 : Stream A #) ->
                     Bisim A # s1 s2 -> (i : Size) ->
                     Bisim B i (map A B f s1 #) (map A B f s2 #)
{
  bisimMapCong .A B f .(scons A # x xs) .(scons A # x ys) (bisimCons A .# x xs ys b) ($ i) =
    bisimCons B i (f x) (map A B f xs #) (map A B f ys #)
      (bisimMapCong A B f xs ys b i)
}

-- Functor identity law: `map (\x -> x) s ~ s`
cofun bisimMapId : (A : Set) -> (s : Stream A #) -> (i : Size) ->
                   Bisim A i (map A A (\ x -> x) s #) s
{
  bisimMapId .A (scons A .# x xs) ($ i) =
    bisimCons A i x (map A A (\ y -> y) xs #) xs (bisimMapId A xs i)
}

-- Stream map-fusion law: `map g (map f s) ~ map (\x -> g (f x)) s`
cofun bisimMapFusion : (A : Set) -> (B : Set) -> (C : Set) ->
                       (f : A -> B) -> (g : B -> C) ->
                       (s : Stream A #) -> (i : Size) ->
                       Bisim C i (map B C g (map A B f s #) #) (map A C (\ x -> g (f x)) s #)
{
  bisimMapFusion .A B C f g (scons A .# x xs) ($ i) =
    bisimCons C i (g (f x))
      (map B C g (map A B f xs #) #)
      (map A C (\ y -> g (f y)) xs #)
      (bisimMapFusion A B C f g xs i)
}

-- Map over constant stream: `map f (repeat a) ~ repeat (f a)`
cofun bisimMapRepeat : (A : Set) -> (B : Set) -> (f : A -> B) -> (a : A) ->
                       (i : Size) -> Bisim B i (map A B f (repeat A a #) #) (repeat B (f a) #)
{
  bisimMapRepeat A B f a ($ i) =
    bisimCons B i (f a)
      (map A B f (repeat A a #) #)
      (repeat B (f a) #)
      (bisimMapRepeat A B f a i)
}

-- Iterate-map commutation: `iterate f (f a) ~ map f (iterate f a)`
cofun bisimIterateMap : (A : Set) -> (f : A -> A) -> (a : A) ->
                        (i : Size) -> Bisim A i (iterate A f (f a) #) (map A A f (iterate A f a #) #)
{
  bisimIterateMap A f a ($ i) =
    bisimCons A i (f a)
      (iterate A f (f (f a)) #)
      (map A A f (iterate A f (f a) #) #)
      (bisimIterateMap A f (f a) i)
}

-- Interleaving evens and odds reconstructs the original stream:
-- `interleave (evens s) (odds s) ~ s` ( emitting 2 bisimCons steps per ($ ($ i)) )
cofun bisimInterleaveEvensOdds : (A : Set) -> (s : Stream A #) -> (i : Size) ->
                                 Bisim A i (interleave A (evens A s #) (odds A s #) #) s
{
  bisimInterleaveEvensOdds .A (scons A .# x (scons .A .# y xs)) ($ ($ i)) =
    bisimCons A ($ i) x
      (interleave A (odds A (scons A # x (scons A # y xs)) #) (evens A xs #) #)
      (scons A # y xs)
      (bisimCons A i y
        (interleave A (evens A xs #) (odds A xs #) #)
        xs
        (bisimInterleaveEvensOdds A xs i))
}

------------------------------------------------------------------------
-- 6. Concrete Evaluations & Verified Prefix Equality Witnesses
------------------------------------------------------------------------

let n0 : Nat = zero
let n1 : Nat = succ n0
let n2 : Nat = succ n1
let n3 : Nat = succ n2
let n4 : Nat = succ n3

let nats : Stream Nat # = from n0 #

-- Concrete bisimulation witnesses at size #
let fusionWitness : Bisim Nat #
      (map Nat Nat succ (map Nat Nat double nats #) #)
      (map Nat Nat (\ x -> succ (double x)) nats #)
  = bisimMapFusion Nat Nat Nat double succ nats #

let interleaveWitness : Bisim Nat #
      (interleave Nat (evens Nat nats #) (odds Nat nats #) #)
      nats
  = bisimInterleaveEvensOdds Nat nats #

-- Extract propositional `Eq (List Nat)` proofs for the first 4 elements via `bisimTakeEq`
eval let fusionPrefixEq : Eq (List Nat)
           (take Nat n4 (map Nat Nat succ (map Nat Nat double nats #) #))
           (take Nat n4 (map Nat Nat (\ x -> succ (double x)) nats #))
  = bisimTakeEq Nat n4
      (map Nat Nat succ (map Nat Nat double nats #) #)
      (map Nat Nat (\ x -> succ (double x)) nats #)
      fusionWitness

eval let interleavePrefixEq : Eq (List Nat)
           (take Nat n4 (interleave Nat (evens Nat nats #) (odds Nat nats #) #))
           (take Nat n4 nats)
  = bisimTakeEq Nat n4
      (interleave Nat (evens Nat nats #) (odds Nat nats #) #)
      nats
      interleaveWitness
