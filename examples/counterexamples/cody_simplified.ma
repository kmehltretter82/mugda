-- Counterexample 2: Roux-Blanqui-Abel limit-ordinal counterexample
-- (adapted from Cody-simplified.ma to Mugda 2008).
--
-- Demonstrates how deep pattern matching across sibling branches of `M`:
--   M .($ ($ ($ i))) (L .($ ($ i)) f) (S .($ ($ i)) (S .($ i) (S i x)))
-- refines a shared size variable across two branches of a constructor.
-- Semantically, `L # emb` has minimal size omega + 1 (a successor of a limit ordinal),
-- not a 3-fold successor ($ ($ ($ i))), so `pre` shifts `emb` while preserving the shape
-- `M (L ...) (S (S (S zero)))`, causing `deep # loop_term` to diverge in Mugda 2008.
--
-- Rejected in bug-fixed Mugda by both the parameter-admissibility fix (Bug 2) and
-- the pattern-refinement invariant `checkNoccDomains` (Bug 1).

data Nat : Set
{ zero : Nat
; succ : Nat -> Nat
}

let three : Nat = succ (succ (succ zero))

sized data O : Size -> Set
{ Z : (i : Size) -> O ($ i)
; S : (i : Size) -> O i -> O ($ i)
; L : (i : Size) -> (Nat -> O i) -> O ($ i)
; M : (i : Size) -> O i -> O i -> O ($ i)
}

fun emb : Nat -> O #
{ emb zero = Z #
; emb (succ n) = S # (emb n)
}

-- Parameterized sized wrapper: hides (O ($ j)) from unpatched szUsed' (Bug 2)
sized data Wrap (+ A : Set) : Size -> Set
{ wrap : (i : Size) -> A -> Wrap A ($ i)
}

fun pre_aux : (j : Size) -> Wrap (O ($ j)) j -> Nat -> O j
{ pre_aux .($ i) (wrap .(O ($ ($ i))) i (Z .($ i))) n = Z i
; pre_aux .($ i) (wrap .(O ($ ($ i))) i (S .($ i) x)) n = x
; pre_aux .($ i) (wrap .(O ($ ($ i))) i (L .($ i) g)) n = g n
; pre_aux .($ i) (wrap .(O ($ ($ i))) i (M .($ i) a b)) n = a
}

let pre : (i : Size) -> (Nat -> O ($ ($ i))) -> Nat -> O ($ i)
  = \ i -> \ f -> \ n -> pre_aux ($ i) (wrap (O ($ ($ i))) i (f (succ n))) n

-- Deep pattern matching on M with dot pattern (L .($ ($ i)) f) (Bug 1)
fun deep : (i : Size) -> O i -> Nat
{ deep .($ ($ ($ ($ i)))) (M .($ ($ ($ i)))
                             (L .($ ($ i)) f)
                             (S .($ ($ i)) (S .($ i) (S i x))))
  = deep ($ ($ ($ i))) (M ($ ($ i))
                          (L ($ i) (pre i f))
                          (f three))
; deep i x = zero
}

let loop_term : O # = M # (L # emb) (emb three)
eval let diverge : Nat = deep # loop_term
