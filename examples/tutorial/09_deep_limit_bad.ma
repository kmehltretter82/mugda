-- Tutorial chapter 9: Pitfalls and soundness
-- Expect: reject (pattern refinement invariant)
-- Deep sibling matching on a limit-ordinal type (`O`) sharing the same size variable `i`
-- across two constructor arguments. At limit ordinal omega + 2, `L # emb` has size
-- omega + 1 (no common predecessor size `i` below omega for all `emb n`), so unifying
-- both branches to `$ i` would fabricate a descending chain. Rejected by `checkNoccDomains`.

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

sized data O : Size -> Set {
  Z : (i : Size) -> O ($ i) ;
  S : (i : Size) -> O i -> O ($ i) ;
  L : (i : Size) -> (Nat -> O i) -> O ($ i) ;
  P : (i : Size) -> O i -> O i -> O ($ i)
}

fun deepLoop : (i : Size) -> O i -> Nat {
  deepLoop .($ ($ i)) (P .($ i) (S i x) (L i f)) =
    deepLoop ($ i) (P i x (f zero))
}
