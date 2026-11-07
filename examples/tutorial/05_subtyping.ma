-- Tutorial chapter 5: Subtyping and variance
-- Expect: accept
-- Every coercion below is the identity function `\ x -> x`. It type-checks
-- only because of size subtyping: a sized inductive type grows with its
-- size (SNat i <= SNat ($ i) <= SNat #); a parameter declared strictly
-- positive with `+` is covariant (SList (SNat i) j <= SList (SNat #) j);
-- function types are contravariant in their domain. The second half shows
-- data types that pass the strict positivity check, including a tree whose
-- children are stored in a list, which is allowed because SList's parameter
-- is declared `+`.

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

sized data SNat : Size -> Set
{
  szero : (i : Size) -> SNat ($ i);
  ssucc : (i : Size) -> SNat i -> SNat ($ i)
}

sized data SList (+ A : Set) : Size -> Set
{
  nil  : (i : Size) -> SList A ($ i);
  cons : (i : Size) -> A -> SList A i -> SList A ($ i)
}

-- sizes are upper bounds, so they can be raised
let wk    : (i : Size) -> SNat i -> SNat ($ i)     = \ i -> \ n -> n
let wk2   : (i : Size) -> SNat i -> SNat ($ ($ i)) = \ i -> \ n -> n
let toInf : (i : Size) -> SNat i -> SNat #         = \ i -> \ n -> n

-- covariance in a `+` parameter, together with the list's own size
let upList : (i : Size) -> (j : Size) -> SList (SNat i) j -> SList (SNat #) # =
  \ i -> \ j -> \ l -> l

-- contravariance: a function that accepts any number also accepts
-- small ones
let narrow : (i : Size) -> (SNat # -> Bool) -> (SNat i -> Bool) =
  \ i -> \ f -> f

-- `$ #` is the same as `#`
let infSucc : SNat ($ #) -> SNat # = \ n -> n

-- a size-preserving function can be used where a weaker type is expected
fun pred : (i : Size) -> SNat i -> SNat i
{
  pred .($ i) (szero i)   = szero i;
  pred .($ i) (ssucc i n) = n
}

let predInf : SNat # -> SNat # = pred #

---------------------------------------------------------------------
-- strict positivity

-- the recursive occurrence is to the right of an arrow: fine
data Ord : Set
{
  ozero : Ord;
  olim  : (Nat -> Ord) -> Ord
}

-- the recursive occurrence is inside a `+` parameter of another type: fine
data Tree (+ A : Set) : Set
{
  node : A -> SList (Tree A) # -> Tree A
}

-- (recursion over such trees needs sizes, see chapter 6)
fun root : (A : Set) -> Tree A -> A
{
  root .A (node A a ts) = a
}

eval let r : Bool = root Bool (node Bool tt (cons (Tree Bool) # (node Bool ff (nil (Tree Bool) #)) (nil (Tree Bool) #)))
