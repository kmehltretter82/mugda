-- Counterexample 1: Karl Mehltretter's 2007 counterexample (examples/loop.ma, Thesis Fig. 5.5),
-- with the non-admissible arguments wrapped in a parameterized sized data type Wrap
-- (completing what examples/loop2.ma and examples/loop3.ma tried to do: "-- hide bad types ....").
--
-- In unpatched Mugda v1.0 (2008), this file passes scope checking, type checking,
-- admissibility checking, and termination checking with zero warnings, and
-- evaluating `start` loops forever.
--
-- In bug-fixed Mugda, it is rejected both by:
--   1. The parameter-admissibility check in `szSizeVarTarget` / `szUsed'` (Bug 2), and
--   2. The pattern-refinement invariant in `checkPattern` (Bug 1).

sized data SNat : Size -> Set
{ zero : (i : Size) -> SNat ($ i)
; succ : (i : Size) -> SNat i -> SNat ($ i)
}

data Maybe (+ A : Set) : Set
{ nothing : Maybe A
; just    : A -> Maybe A
}

sized data Wrap (+ A : Set) : Size -> Set
{ wrap : (i : Size) -> A -> Wrap A ($ i)
}

let Nat : Set = SNat #

fun shift_case : (j : Size) -> Wrap (Maybe (SNat ($ j))) j -> Maybe (SNat j)
{ shift_case .($ i) (wrap .(Maybe (SNat ($ ($ i)))) i (nothing .(SNat ($ ($ i))))) = nothing (SNat ($ i))
; shift_case .($ i) (wrap .(Maybe (SNat ($ ($ i)))) i (just .(SNat ($ ($ i))) (zero .($ i)))) = nothing (SNat ($ i))
; shift_case .($ i) (wrap .(Maybe (SNat ($ ($ i)))) i (just .(SNat ($ ($ i))) (succ .($ i) x))) = just (SNat ($ i)) x
}

let shift : (i : Size) -> (Nat -> Maybe (SNat ($ ($ i)))) -> Nat -> Maybe (SNat ($ i))
  = \ i -> \ f -> \ n -> shift_case ($ i) (wrap (Maybe (SNat ($ ($ i)))) i (f (succ # n)))

let inc : Nat -> Maybe Nat = \ n -> just Nat (succ # (succ # n))

data Unit : Set
{ unit : Unit
}

mutual
{
  fun loop : (j : Size) -> SNat j -> Wrap (Nat -> Maybe (SNat j)) j -> Unit
  { loop .($ i) (zero i) (wrap .(Nat -> Maybe (SNat ($ i))) .i f)
      = loop_case ($ i) (wrap (Nat -> Maybe (SNat ($ i))) i f) (wrap (Maybe (SNat ($ i))) i (f (zero #)))
  ; loop .($ ($ i)) (succ .($ i) (zero i)) (wrap .(Nat -> Maybe (SNat ($ ($ i)))) .($ i) f)
      = loop ($ i) (zero i) (wrap (Nat -> Maybe (SNat ($ i))) i (shift i f))
  ; loop .($ ($ i)) (succ .($ i) (succ i n)) (wrap .(Nat -> Maybe (SNat ($ ($ i)))) .($ i) f)
      = loop ($ i) (succ i n) (wrap (Nat -> Maybe (SNat ($ i))) i (shift i f))
  }

  fun loop_case : (j : Size) -> Wrap (Nat -> Maybe (SNat j)) j -> Wrap (Maybe (SNat j)) j -> Unit
  { loop_case .($ i) wf (wrap .(Maybe (SNat ($ i))) i (nothing .(SNat ($ i)))) = unit
  ; loop_case .($ i) wf (wrap .(Maybe (SNat ($ i))) .i (just .(SNat ($ i)) (zero i))) = unit
  ; loop_case .($ ($ i)) (wrap .(Nat -> Maybe (SNat ($ ($ i)))) .($ i) f) (wrap .(Maybe (SNat ($ ($ i)))) .($ i) (just .(SNat ($ ($ i))) (succ .($ i) (zero i))))
      = loop ($ i) (zero i) (wrap (Nat -> Maybe (SNat ($ i))) i (shift i f))
  ; loop_case .($ ($ i)) (wrap .(Nat -> Maybe (SNat ($ ($ i)))) .($ i) f) (wrap .(Maybe (SNat ($ ($ i)))) .($ i) (just .(SNat ($ ($ i))) (succ .($ i) (succ i y))))
      = loop ($ i) (succ i y) (wrap (Nat -> Maybe (SNat ($ i))) i (shift i f))
  }
}

let start : Unit = loop # (zero #) (wrap (Nat -> Maybe Nat) # inc)
