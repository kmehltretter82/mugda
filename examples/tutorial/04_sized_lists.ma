-- Tutorial chapter 4: Sized lists and sorting
-- Expect: accept
-- Sized lists. `map`, `filter` and `partition` get types saying that their
-- output is no longer than their input (size `i` in, size `i` out). With
-- those types, quicksort and mergesort are accepted: their recursive calls
-- are on lists of size `i` while the input had size `$ i`. `filter` and
-- `partition` rely on subtyping, SList A i <= SList A ($ i), whenever they
-- drop an element.

data Bool : Set
{
  tt : Bool;
  ff : Bool
}

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt a b = a;
  ite A ff a b = b
}

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

fun leq : Nat -> Nat -> Bool
{
  leq zero     y        = tt;
  leq (succ x) zero     = ff;
  leq (succ x) (succ y) = leq x y
}

-- `+ A` declares the parameter strictly positive (chapter 5); it makes
-- SList covariant in A
sized data SList (+ A : Set) : Size -> Set
{
  nil  : (i : Size) -> SList A ($ i);
  cons : (i : Size) -> A -> SList A i -> SList A ($ i)
}

data Prod (+ A : Set) : Set
{
  prod : A -> A -> Prod A
}

fun fst : (A : Set) -> Prod A -> A
{
  fst .A (prod A a b) = a
}

fun snd : (A : Set) -> Prod A -> A
{
  snd .A (prod A a b) = b
}

-- size preserving
fun map : (A : Set) -> (B : Set) -> (A -> B) -> (i : Size) -> SList A i -> SList B i
{
  map .A B f .($ i) (nil A i)       = nil B i;
  map .A B f .($ i) (cons A i x xs) = cons B i (f x) (map A B f i xs)
}

-- the result is bounded by the input; when `x` is dropped,
-- `rec : SList A i` is used at type SList A ($ i) by subtyping
fun filter : (A : Set) -> (A -> Bool) -> (i : Size) -> SList A i -> SList A i
{
  filter .A p .($ i) (nil A i) = nil A i;
  filter .A p .($ i) (cons A i x xs) =
    let rec : SList A i = filter A p i xs in
    ite (SList A ($ i)) (p x) (cons A i x rec) rec
}

-- both halves are bounded by the input
fun partition : (A : Set) -> (A -> Bool) -> (i : Size) -> SList A i -> Prod (SList A i)
{
  partition .A p .($ i) (nil A i) = prod (SList A ($ i)) (nil A i) (nil A i);
  partition .A p .($ i) (cons A i x xs) =
    let rec : Prod (SList A i) = partition A p i xs in
    let l1  : SList A i = fst (SList A i) rec in
    let l2  : SList A i = snd (SList A i) rec in
    ite (Prod (SList A ($ i))) (p x)
        (prod (SList A ($ i)) (cons A i x l1) l2)
        (prod (SList A ($ i)) l1 (cons A i x l2))
}

fun append : (A : Set) -> (i : Size) -> SList A i -> SList A # -> SList A #
{
  append .A .($ i) (nil A i)       ys = ys;
  append .A .($ i) (cons A i x xs) ys = cons A # x (append A i xs ys)
}

-- the recursive calls are at size i, the input had size $ i
fun qsort : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i -> SList A #
{
  qsort .A le .($ i) (nil A i) = nil A #;
  qsort .A le .($ i) (cons A i x xs) =
    let halves : Prod (SList A i) = partition A (\ y -> le y x) i xs in
    append A # (qsort A le i (fst (SList A i) halves))
               (cons A # x (qsort A le i (snd (SList A i) halves)))
}

-- mergesort: `split` deals the elements alternately into two lists,
-- each bounded by the input
fun split : (A : Set) -> (i : Size) -> SList A i -> Prod (SList A i)
{
  split .A .($ i) (nil A i) = prod (SList A ($ i)) (nil A i) (nil A i);
  split .A .($ i) (cons A i x xs) =
    let rec : Prod (SList A i) = split A i xs in
    prod (SList A ($ i)) (cons A i x (snd (SList A i) rec)) (fst (SList A i) rec)
}

-- merging needs no sizes: in each call one of the two lists gets shorter,
-- and the size-change principle sees that
fun merge : (A : Set) -> (A -> A -> Bool) -> SList A # -> SList A # -> SList A #
{
  merge .A le (nil A .#) ys = ys;
  merge .A le (cons A .# x xs) (nil .A .#) = cons A # x xs;
  merge .A le (cons A .# x xs) (cons .A .# y ys) =
    ite (SList A #) (le x y)
        (cons A # x (merge A le xs (cons A # y ys)))
        (cons A # y (merge A le (cons A # x xs) ys))
}

-- the list must have at least two elements before we split it: the
-- recursive calls are on `cons a l1` and `cons b l2` with l1, l2 : SList A i,
-- i.e. at size $ i, while the input had size $ $ i
fun msort : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i -> SList A #
{
  msort .A le .($ i) (nil A i) = nil A #;
  msort .A le .($ ($ i)) (cons .A .($ i) a (nil A i)) = cons A # a (nil A #);
  msort .A le .($ ($ i)) (cons .A .($ i) a (cons A i b xs)) =
    let halves : Prod (SList A i) = split A i xs in
    merge A le (msort A le ($ i) (cons A i a (fst (SList A i) halves)))
               (msort A le ($ i) (cons A i b (snd (SList A i) halves)))
}

let one   : Nat = succ zero
let two   : Nat = succ one
let three : Nat = succ two
let four  : Nat = succ three

let list : SList Nat # =
  cons Nat # three (cons Nat # one (cons Nat # four (cons Nat # zero (cons Nat # two (nil Nat #)))))

eval let doubled : SList Nat # = map Nat Nat (\ n -> succ n) # list
eval let small   : SList Nat # = filter Nat (\ n -> leq n two) # list
eval let qsorted : SList Nat # = qsort Nat leq # list
eval let msorted : SList Nat # = msort Nat leq # list
