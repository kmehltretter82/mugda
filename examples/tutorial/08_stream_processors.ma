-- Tutorial chapter 8: Mixing induction and coinduction
-- Expect: accept
-- Stream processors (thesis Section 5.5.4, examples/sp.ma). A processor
-- reads (`get`) finitely many input elements before it writes (`put`) one
-- output element, and it does this forever. The "finitely many gets"
-- part is the inductive type ISP. The "forever" part is the coinductive
-- type SP, which wraps one ISP round whose continuation is again an SP.
-- `ieat` runs one inductive round and terminates by structural recursion;
-- `eat` is productive because its corecursive call, buried inside the
-- continuation passed to `ieat`, is at the smaller size `i`.

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

data List (+ A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

sized codata Stream : Size -> Set
{
  scons : (i : Size) -> Nat -> Stream i -> Stream ($ i)
}

fun head : Stream # -> Nat
{
  head (scons .# x xs) = x
}

fun tail : Stream # -> Stream #
{
  tail (scons .# x xs) = xs
}

fun take : Nat -> Stream # -> List Nat
{
  take zero     s = nil Nat;
  take (succ n) s = cons Nat (head s) (take n (tail s))
}

cofun from : Nat -> (i : Size) -> Stream i
{
  from n ($ i) = scons i n (from (succ n) i)
}

-- one round: some gets, then a put with the continuation K
data ISP (+ K : Set) : Set
{
  put : Nat -> K -> ISP K;
  get : (Nat -> ISP K) -> ISP K
}

-- infinitely many rounds
sized codata SP : Size -> Set
{
  isp : (i : Size) -> ISP (SP i) -> SP ($ i)
}

-- run one round on the input; hand the output element, the continuation
-- and the rest of the input to `h`
fun ieat : (K : Set) -> (C : Set) -> ISP K -> Stream # -> (Nat -> K -> Stream # -> C) -> C
{
  ieat .K C (get K f)   (scons .# a as) h = ieat K C (f a) as h;
  ieat .K C (put K b k) as              h = h b k as
}

-- run a processor forever
cofun eat : SP # -> Stream # -> (i : Size) -> Stream i
{
  eat (isp .# ip) as ($ i) =
    ieat (SP #) (Stream ($ i)) ip as
         (\ b -> \ k -> \ as' -> scons i b (eat k as' i))
}

-- examples: double every element; add up pairs of elements
cofun doubler : (i : Size) -> SP i
{
  doubler ($ i) = isp i (get (SP i) (\ n -> put (SP i) (add n n) (doubler i)))
}

cofun pairSum : (i : Size) -> SP i
{
  pairSum ($ i) =
    isp i (get (SP i) (\ m -> get (SP i) (\ n -> put (SP i) (add m n) (pairSum i))))
}

-- echo every element twice: two puts in one round
cofun stutter : (i : Size) -> SP i
{
  stutter ($ ($ i)) =
    isp ($ i) (get (SP ($ i)) (\ n -> put (SP ($ i)) n (isp i (put (SP i) n (stutter i)))))
}

let four : Nat = succ (succ (succ (succ zero)))

eval let doubled : List Nat = take four (eat (doubler #) (from zero #) #)
eval let summed  : List Nat = take four (eat (pairSum #) (from zero #) #)
eval let stutt   : List Nat = take four (eat (stutter #) (from zero #) #)
