-- Tutorial chapter 6: Higher-order and nested data
-- Expect: accept
-- Sizes for data that is not first-order: Brouwer ordinals (infinitely
-- branching), rose trees whose children are a sized list, and a function
-- that takes a size-preserving function as an argument. In `mapT` and
-- `flat` the recursive function is passed, partially applied, to `mapL`.
-- The checker cannot see the call that `mapL` will make, but the size
-- argument of the partial application is already `i`, smaller than the
-- `$ i` of the input tree, and that is enough.

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

---------------------------------------------------------------------
-- sized Brouwer ordinals

sized data SOrd : Size -> Set
{
  ozero : (i : Size) -> SOrd ($ i);
  olim  : (i : Size) -> (Nat -> SOrd i) -> SOrd ($ i)
}

-- recursion on the size argument; `f n : SOrd i` and i < $ i
fun addOrd : SOrd # -> (i : Size) -> SOrd i -> SOrd #
{
  addOrd x .($ i) (ozero i)  = x;
  addOrd x .($ i) (olim i f) = olim # (\ n -> addOrd x i (f n))
}

fun fromNat : Nat -> SOrd #
{
  fromNat zero     = ozero #;
  fromNat (succ n) = olim # (\ m -> fromNat n)
}

let omega : SOrd # = olim # fromNat
let omegaPlusOmega : SOrd # = addOrd omega # omega

---------------------------------------------------------------------
-- rose trees

sized data SList (+ A : Set) : Size -> Set
{
  nil  : (i : Size) -> SList A ($ i);
  cons : (i : Size) -> A -> SList A i -> SList A ($ i)
}

fun mapL : (A : Set) -> (B : Set) -> (A -> B) -> (i : Size) -> SList A i -> SList B i
{
  mapL .A B f .($ i) (nil A i)       = nil B i;
  mapL .A B f .($ i) (cons A i x xs) = cons B i (f x) (mapL A B f i xs)
}

fun append : (A : Set) -> (i : Size) -> SList A i -> SList A # -> SList A #
{
  append .A .($ i) (nil A i)       ys = ys;
  append .A .($ i) (cons A i x xs) ys = cons A # x (append A i xs ys)
}

fun concat : (A : Set) -> (i : Size) -> SList (SList A #) i -> SList A #
{
  concat A .($ i) (nil .(SList A #) i)       = nil A #;
  concat A .($ i) (cons .(SList A #) i l ls) = append A # l (concat A i ls)
}

-- the children of a tree of size $ i are trees of size i,
-- stored in a list of any length
sized data Tree (+ A : Set) : Size -> Set
{
  leaf : (i : Size) -> A -> Tree A ($ i);
  node : (i : Size) -> SList (Tree A i) # -> Tree A ($ i)
}

fun mapT : (A : Set) -> (B : Set) -> (A -> B) -> (i : Size) -> Tree A i -> Tree B i
{
  mapT .A B f .($ i) (leaf A i a)  = leaf B i (f a);
  mapT .A B f .($ i) (node A i ts) =
    node B i (mapL (Tree A i) (Tree B i) (mapT A B f i) # ts)
}

fun flat : (A : Set) -> (i : Size) -> Tree A i -> SList A #
{
  flat .A .($ i) (leaf A i a)  = cons A # a (nil A #);
  flat .A .($ i) (node A i ts) =
    concat A # (mapL (Tree A i) (SList A #) (flat A i) # ts)
}

let one   : Nat = succ zero
let two   : Nat = succ one
let three : Nat = succ two

-- node [leaf 1, node [leaf 2, leaf 3]]
let tree : Tree Nat # =
  node Nat # (cons (Tree Nat #) # (leaf Nat # one)
             (cons (Tree Nat #) # (node Nat # (cons (Tree Nat #) # (leaf Nat # two)
                                              (cons (Tree Nat #) # (leaf Nat # three)
                                              (nil (Tree Nat #) #))))
             (nil (Tree Nat #) #)))

eval let leaves  : SList Nat # = flat Nat # tree
eval let leaves2 : SList Nat # = flat Nat # (mapT Nat Nat (\ n -> succ n) # tree)

---------------------------------------------------------------------
-- a size-preserving function as an argument (thesis Section 5.4.4)

sized data SNat : Size -> Set
{
  szero : (i : Size) -> SNat ($ i);
  ssucc : (i : Size) -> SNat i -> SNat ($ i)
}

-- "one-two-eliminate": size preserving, so it fits the argument type of
-- addWith
fun ote : (i : Size) -> SNat i -> SNat i
{
  ote .($ i)     (szero i)                  = szero i;
  ote .($ ($ i)) (ssucc .($ i) (szero i))   = szero i;
  ote .($ ($ i)) (ssucc .($ i) (ssucc i x)) = ssucc ($ i) (ssucc i (ote i x))
}

-- the two size arguments swap in the recursive call: both the size types
-- (to know `f j y : SNat j`) and the size-change principle (for the swap)
-- are needed
fun addWith : ((k : Size) -> SNat k -> SNat k) ->
              (i : Size) -> (j : Size) -> SNat i -> SNat j -> SNat #
{
  addWith f .($ i) j (szero i)   y = y;
  addWith f .($ i) j (ssucc i x) y = ssucc # (addWith f j i (f j y) (f i x))
}

let s3 : SNat # = ssucc # (ssucc # (ssucc # (szero #)))
let s4 : SNat # = ssucc # s3

eval let sum : SNat # = addWith ote # # s4 s3
