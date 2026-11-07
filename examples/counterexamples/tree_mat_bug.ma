-- Counterexample 5: Pure first-order non-sized binary tree counterexample to
-- the Matrix Order `ORDER_+` (`maxO (Mat m1) (Mat m2)` in Termination.hs, Bug 3,
-- analogous to Andreas Abel's BugInMatOrder.ma).
--
-- Uses NO sized types and NO dot patterns at all!
-- In unpatched Mugda 2008:
--   - `f (node x y) = g (node x (node y y))` compares `(node x (node y y))` against
--     `(node x y)` using `Mat [[Eq, Un], [Un, Un]]` (from `x`) combined via entrywise
--     `maxO` with `Mat [[Un, Un], [Un, Lt]]` (Had-style from `y`), yielding a matrix with
--     diagonal `[Eq, Un]`.
--   - Composing `f -> g` with `g -> f` (which has `[Un, Lt]` in `subterm (node x y) y`)
--     produces an idempotent call matrix whose diagonal has `Lt`, so Mugda 2008 accepts
--     the mutual block!
--   - At runtime: `f (node leaf leaf) -> g (node leaf (node leaf leaf)) -> f (node leaf leaf)`
--     loops forever in a 2-step cycle!
--
-- Rejected in bug-fixed Mugda because `maxO (Mat _) (Mat _)` collapses to `Un` rather than
-- adding matrices entrywise across distinct pattern variables.

data Tree : Set
{ leaf : Tree
; node : Tree -> Tree -> Tree
}

mutual
{
  fun f : Tree -> Tree
  { f leaf = leaf
  ; f (node x y) = g (node x (node y y))
  }

  fun g : Tree -> Tree
  { g leaf = leaf
  ; g (node x y) = f y
  }
}
