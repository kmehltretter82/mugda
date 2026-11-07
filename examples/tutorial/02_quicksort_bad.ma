-- Tutorial chapter 2: Termination without sizes
-- Expect: reject (termination)
-- Quicksort on unsized lists (compare examples/qsort.ma). `partition`
-- splits the tail into the elements below and above the pivot, and the
-- recursive calls are on the two halves. They are not syntactic subterms of
-- the input, so the termination checker gives up. Chapter 4 shows the
-- sized version, which is accepted.

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

data List (A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

data Prod (A : Set) : Set
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

fun ite : (A : Set) -> Bool -> A -> A -> A
{
  ite A tt a b = a;
  ite A ff a b = b
}

fun partition : (A : Set) -> (A -> Bool) -> List A -> Prod (List A)
{
  partition .A p (nil A) = prod (List A) (nil A) (nil A);
  partition .A p (cons A x xs) =
    let rec : Prod (List A) = partition A p xs in
    ite (Prod (List A)) (p x)
        (prod (List A) (cons A x (fst (List A) rec)) (snd (List A) rec))
        (prod (List A) (fst (List A) rec) (cons A x (snd (List A) rec)))
}

fun append : (A : Set) -> List A -> List A -> List A
{
  append .A (nil A)       ys = ys;
  append .A (cons A x xs) ys = cons A x (append A xs ys)
}

fun qsort : (A : Set) -> (A -> A -> Bool) -> List A -> List A
{
  qsort .A le (nil A) = nil A;
  qsort .A le (cons A x xs) =
    let halves : Prod (List A) = partition A (\ y -> le y x) xs in
    append A (qsort A le (fst (List A) halves))
             (cons A x (qsort A le (snd (List A) halves)))
}
