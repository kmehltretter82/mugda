-- Tutorial chapter 4: Sized lists and sorting
-- Expect: reject (termination)
-- The same quicksort as in 04_sized_lists.ma, except that `partition` has
-- the weaker type `SList A i -> Prod (SList A #)`. The halves now have
-- size `#`, so quicksort has to call itself at size `#`, and the
-- comparison of `#` with the pattern `.($ i)` gives "?". The termination
-- check fails. The fix is to give `partition` its precise type back.

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

fun partition : (A : Set) -> (A -> Bool) -> (i : Size) -> SList A i -> Prod (SList A #)
{
  partition .A p .($ i) (nil A i) = prod (SList A #) (nil A #) (nil A #);
  partition .A p .($ i) (cons A i x xs) =
    let rec : Prod (SList A #) = partition A p i xs in
    let l1  : SList A # = fst (SList A #) rec in
    let l2  : SList A # = snd (SList A #) rec in
    ite (Prod (SList A #)) (p x)
        (prod (SList A #) (cons A # x l1) l2)
        (prod (SList A #) l1 (cons A # x l2))
}

fun append : (A : Set) -> (i : Size) -> SList A i -> SList A # -> SList A #
{
  append .A .($ i) (nil A i)       ys = ys;
  append .A .($ i) (cons A i x xs) ys = cons A # x (append A i xs ys)
}

fun qsort : (A : Set) -> (A -> A -> Bool) -> (i : Size) -> SList A i -> SList A #
{
  qsort .A le .($ i) (nil A i) = nil A #;
  qsort .A le .($ i) (cons A i x xs) =
    let halves : Prod (SList A #) = partition A (\ y -> le y x) i xs in
    append A # (qsort A le # (fst (SList A #) halves))
               (cons A # x (qsort A le # (snd (SList A #) halves)))
}
