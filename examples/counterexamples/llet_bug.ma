-- Counterexample 6: `let`-expression termination bug (Bug 4, Termination.hs line 307 & Thesis p. 41).
--
-- In Abstract.hs, `LLet` is defined as `LLet Name Type Expr Expr` (`let x : t = e1 in e2`).
-- However, `collectCalls` in Termination.hs line 307 wrote:
--   `LLet _ e1 t1 e2 -> collect e1 ++ collect e2`
-- swapping the type `t1` and bound expression `e1`, and then omitting `t1`!
-- As a result, any recursive call inside the bound expression `e1` of a `let` was
-- completely invisible to the termination checker in Mugda 2008.
--
-- Rejected in bug-fixed Mugda (`Termination check for function loop fails`).

data Nat : Set
{ zero : Nat
; succ : Nat -> Nat
}

fun loop : Nat -> Nat
{ loop x = let y : Nat = loop x in y
}
