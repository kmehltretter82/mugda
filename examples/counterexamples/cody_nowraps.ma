-- Counterexample 3: Pure sibling pattern-refinement violation without any Wrap type.
--
-- Shows that even with an admissible signature `(i : Size) -> O i -> Nat -> O ($ i)`,
-- matching both branches of `M .($ i) (L .i f) (S .i (S i x))` in unpatched Mugda 2008
-- unsoundly forces `f : Nat -> O ($ i)` in the left branch using the successor
-- refinement from `S .i (S i x)` in the right branch.
--
-- Rejected in bug-fixed Mugda by `checkNoccDomains` (Bug 1).

data Nat : Set
{ zero : Nat
; succ : Nat -> Nat
}

sized data O : Size -> Set
{ Z : (i : Size) -> O ($ i)
; S : (i : Size) -> O i -> O ($ i)
; L : (i : Size) -> (Nat -> O i) -> O ($ i)
; M : (i : Size) -> O i -> O i -> O ($ i)
}

fun extract : (i : Size) -> O i -> Nat -> O ($ i)
{ extract .($ ($ i)) (M .($ i) (L .i f) (S .i (S i x))) n = f n
; extract i x n = Z i
}
