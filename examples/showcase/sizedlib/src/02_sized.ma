
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
