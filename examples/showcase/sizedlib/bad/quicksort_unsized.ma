-- Expect: reject (Termination check fails: quicksort without sizes)
--
-- The quicksort of sizedlib (src/02_sized.ma) with the size annotations
-- removed: `List A` instead of `SList A i`.  The recursive calls of
-- qsapp are on the results of `partition`, which are not subterms of
-- the input list.  Without the size index i, which says that partition
-- returns lists no longer than its input, the size-change termination
-- checker cannot prove termination.

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

data List (+ A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

fun partition : (A : Set) -> (A -> Bool) -> List A -> Prod (List A) (List A)
{
  partition .A p (nil A) = pair (List A) (List A) (nil A) (nil A);
  partition .A p (cons A x xs) =
    let rec : Prod (List A) (List A) = partition A p xs in
    let l1  : List A = fst (List A) (List A) rec in
    let l2  : List A = snd (List A) (List A) rec in
    ite (Prod (List A) (List A)) (p x)
        (pair (List A) (List A) (cons A x l1) l2)
        (pair (List A) (List A) l1 (cons A x l2))
}

fun qsapp : (A : Set) -> (A -> A -> Bool) -> List A -> List A -> List A
{
  qsapp .A le (nil A)       acc = acc;
  qsapp .A le (cons A x xs) acc =
    let pv    : Prod (List A) (List A) = partition A (\ y -> le y x) xs in
    let small : List A = fst (List A) (List A) pv in
    let big   : List A = snd (List A) (List A) pv in
    qsapp A le small (cons A x (qsapp A le big acc))
}
