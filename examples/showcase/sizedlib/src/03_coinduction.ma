
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
