-- Tutorial chapter 8: Mixing induction and coinduction
-- Expect: reject (termination)
-- A "processor" that reads forever and never writes. If this value of the
-- inductive type ISP existed, `eat` from 08_stream_processors.ma would
-- never produce the next output element. Because ISP is inductive, the
-- only way to build it is by a recursive `fun`. That fun calls itself with
-- the same argument, so the termination check rejects it.

data Nat : Set
{
  zero : Nat;
  succ : Nat -> Nat
}

data ISP (+ K : Set) : Set
{
  put : Nat -> K -> ISP K;
  get : (Nat -> ISP K) -> ISP K
}

fun sink : (K : Set) -> ISP K
{
  sink K = get K (\ n -> sink K)
}
