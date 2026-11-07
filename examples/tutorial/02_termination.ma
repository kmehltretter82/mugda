-- Tutorial chapter 2: Termination without sizes
-- Expect: accept
-- Programs that the size-change termination (SCT) checker accepts without
-- any size annotations: plain structural recursion, recursion with permuted
-- arguments, Ackermann's function (a lexicographic descent), mutual
-- recursion, recursion through a function-typed field of a Brouwer ordinal,
-- and nested patterns on pairs and lists of lists, which need the extended
-- order ORDER+ of the thesis (Section 4.6).

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

-- structural: call matrix  add ( <= ? ; ? < ) add
fun add : Nat -> Nat -> Nat
{
  add x zero     = x;
  add x (succ y) = succ (add x y)
}

-- permuted arguments: no single argument decreases in every call,
-- but every idempotent call matrix has a < on its diagonal
fun add2 : Nat -> Nat -> Nat
{
  add2 x zero     = x;
  add2 x (succ y) = succ (add2 y x)
}

-- lexicographic descent, including a nested recursive call
fun ack : Nat -> Nat -> Nat
{
  ack zero     y        = succ y;
  ack (succ x) zero     = ack x (succ zero);
  ack (succ x) (succ y) = ack x (ack (succ x) y)
}

-- mutual recursion: `mutual { ... }` groups declarations into one
-- call graph
mutual
{
  fun even : Nat -> Bool
  {
    even zero     = tt;
    even (succ x) = odd x
  }

  fun odd : Nat -> Bool
  {
    odd zero     = ff;
    odd (succ x) = even x
  }
}

-- Brouwer ordinals: an infinitely branching inductive type
data Ord : Set
{
  ozero : Ord;
  olim  : (Nat -> Ord) -> Ord
}

-- `f n` counts as smaller than `olim f`: f n <= f (Axiom 2) and
-- f < olim f (Axiom 1)
fun addOrd : Ord -> Ord -> Ord
{
  addOrd x ozero    = x;
  addOrd x (olim f) = olim (\ n -> addOrd x (f n))
}

-- nested patterns: the extended order compares the components of `pair`
-- separately, so the swap inside the pair is still recognised
data Pair : Set
{
  pair : Nat -> Nat -> Pair
}

fun addpair : Pair -> Nat
{
  addpair (pair x zero)     = x;
  addpair (pair x (succ y)) = succ (addpair (pair y x))
}

fun ackp : Pair -> Nat
{
  ackp (pair zero y)            = succ y;
  ackp (pair (succ x) zero)     = ackp (pair x (succ zero));
  ackp (pair (succ x) (succ y)) = ackp (pair x (ackp (pair (succ x) y)))
}

-- flattening a list of lists: the argument of the recursive call
-- `lcons xl yl` is not a subterm of the pattern, but componentwise
-- it is smaller-or-equal and strictly smaller in the first component
data NList : Set
{
  nnil  : NList;
  ncons : Nat -> NList -> NList
}

data LList : Set
{
  lnil  : LList;
  lcons : NList -> LList -> LList
}

fun flat : LList -> NList
{
  flat lnil                    = nnil;
  flat (lcons nnil yl)         = flat yl;
  flat (lcons (ncons x xl) yl) = ncons x (flat (lcons xl yl))
}

let one   : Nat = succ zero
let two   : Nat = succ one
let three : Nat = succ two

eval let five  : Nat  = add2 two three
eval let ack22 : Nat  = ack two two
eval let ack11 : Nat  = ackp (pair one one)
eval let odd3  : Bool = odd three
eval let flat1 : NList =
  flat (lcons (ncons one (ncons two nnil)) (lcons nnil (lcons (ncons three nnil) lnil)))
