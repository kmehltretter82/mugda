-- Tutorial chapter 8: Mixing induction and coinduction
-- Expect: reject (termination)
-- What goes wrong if `get` is coinductive too? Here CSP has both `cput`
-- and `cget` as coinductive constructors, so `sink`, which only reads, is
-- a perfectly productive CSP and is accepted. But running a CSP on a
-- stream is no longer productive: in the `cget` case `run` calls itself
-- at the same size `$ i`, and `f a` is not smaller than `cget .# f`,
-- because codata is not well-founded. The checker rejects `run`. This is
-- why the processors in 08_stream_processors.ma keep `get` inductive.

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

sized codata Stream : Size -> Set
{
  scons : (i : Size) -> Nat -> Stream i -> Stream ($ i)
}

sized codata CSP : Size -> Set
{
  cput : (i : Size) -> Nat -> CSP i -> CSP ($ i);
  cget : (i : Size) -> (Nat -> CSP i) -> CSP ($ i)
}

-- accepted: a productive CSP that only ever reads
cofun sink : (i : Size) -> CSP i
{
  sink ($ i) = cget i (\ n -> sink i)
}

-- rejected
cofun run : CSP # -> Stream # -> (i : Size) -> Stream i
{
  run (cput .# b k) as              ($ i) = scons i b (run k as i);
  run (cget .# f)   (scons .# a as) ($ i) = run (f a) as ($ i)
}
