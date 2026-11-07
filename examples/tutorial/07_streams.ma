-- Tutorial chapter 7: Coinduction
-- Expect: accept
-- Sized coinductive streams. For codata the size is a lower bound on how
-- far the stream is defined, so subtyping runs the other way:
-- Stream A # <= Stream A ($ i) <= Stream A i. A `cofun` is productive if it
-- is defined by matching on a successor size `($ i)` and only calls itself
-- at size `i`. The termination checker then sees a decreasing size, as for
-- an ordinary recursive function. head, tail and nth are ordinary `fun`s
-- on fully defined streams, `Stream A #`.

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

sized codata Stream (+ A : Set) : Size -> Set
{
  scons : (i : Size) -> A -> Stream A i -> Stream A ($ i)
}

-- observations on fully defined streams
fun head : (A : Set) -> Stream A # -> A
{
  head .A (scons A .# x xs) = x
}

fun tail : (A : Set) -> Stream A # -> Stream A #
{
  tail .A (scons A .# x xs) = xs
}

fun take : (A : Set) -> Nat -> Stream A # -> List A
{
  take A zero     s = nil A;
  take A (succ n) s = cons A (head A s) (take A n (tail A s))
}

fun nth : (A : Set) -> Nat -> Stream A # -> A
{
  nth A zero     s = head A s;
  nth A (succ n) s = nth A n (tail A s)
}

-- productive definitions: match on ($ i), call at i
cofun repeat : (A : Set) -> A -> (i : Size) -> Stream A i
{
  repeat A a ($ i) = scons A i a (repeat A a i)
}

cofun from : Nat -> (i : Size) -> Stream Nat i
{
  from n ($ i) = scons Nat i n (from (succ n) i)
}

-- stream arguments are fully defined streams (size #);
-- only the result is sized
cofun map : (A : Set) -> (B : Set) -> (A -> B) -> Stream A # -> (i : Size) -> Stream B i
{
  map .A B f (scons A .# x xs) ($ i) = scons B i (f x) (map A B f xs i)
}

cofun zipWith : (A : Set) -> (B : Set) -> (C : Set) -> (A -> B -> C) ->
                Stream A # -> Stream B # -> (i : Size) -> Stream C i
{
  zipWith .A .B C f (scons A .# a as) (scons B .# b bs) ($ i) =
    scons C i (f a b) (zipWith A B C f as bs i)
}

-- Fibonacci with two accumulators
cofun fibFrom : Nat -> Nat -> (i : Size) -> Stream Nat i
{
  fibFrom x y ($ i) = scons Nat i x (fibFrom y (add x y) i)
}

-- two elements per step is fine as long as the sizes match up
cofun twoAtATime : Nat -> (i : Size) -> Stream Nat i
{
  twoAtATime n ($ ($ i)) = scons Nat ($ i) n (scons Nat i n (twoAtATime (succ n) i))
}

-- mutual corecursion
mutual
{
  cofun ticks : (i : Size) -> Stream Bool i
  {
    ticks ($ i) = scons Bool i tt (tocks i)
  }

  cofun tocks : (i : Size) -> Stream Bool i
  {
    tocks ($ i) = scons Bool i ff (ticks i)
  }
}

-- coinductive subtyping: a fully defined stream can be used at any size,
-- and a stream defined to depth $ i is also defined to depth i
let anySize : (A : Set) -> (i : Size) -> Stream A # -> Stream A i = \ A -> \ i -> \ s -> s
let shallow : (A : Set) -> (i : Size) -> Stream A ($ i) -> Stream A i = \ A -> \ i -> \ s -> s

let one   : Nat = succ zero
let two   : Nat = succ one
let three : Nat = succ two
let four  : Nat = succ three
let five  : Nat = succ four

let nats : Stream Nat # = from zero #
let fibs : Stream Nat # = fibFrom one one #

-- a stream is printed as an unevaluated corecursive call...
eval let natsValue : Stream Nat # = nats
-- ...so we look at finite prefixes
eval let natsPrefix : List Nat = take Nat four nats
eval let evens      : List Nat = take Nat four (zipWith Nat Nat Nat add nats nats #)
eval let fibPrefix  : List Nat = take Nat five fibs
eval let fib4       : Nat      = nth Nat four fibs
eval let pairs      : List Nat = take Nat five (twoAtATime zero #)
eval let clock      : List Bool = take Bool three (ticks #)
eval let mapped     : List Nat = take Nat three (map Nat Nat succ (repeat Nat zero #) #)
