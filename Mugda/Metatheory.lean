/-
  Mugda/Metatheory.lean
  =====================
  Stage II in-place metatheorems, tightness proofs, and end-to-end verification
  suite proved directly on the Constructive Lean 4 compiler (`Mugda.Core`).
-/

import Mugda.Core
import Mugda.Soundness

namespace MugdaCore

/-! ## 1. Size Subtyping & Erasure Metatheorems (Pillars II & III) -/

/-- **Theorem 1 (Runtime Size Idempotence at `#`)**:
    In `MugdaCore.sinfty` (`Value.hs` line 130), `$ # = #`. -/
theorem sinfty_infty : sinfty .VInfty = .VInfty := rfl

/-- **Theorem 2 (`completePatterns` Rejects `SuccP`)**:
    The ported `cp` checker rejects any `SuccP` pattern immediately (`Completness.hs` line 15). -/
theorem cp_succP_false (p : Pattern) : cp (.SuccP p) = false := rfl

/-- **Theorem 3 (`leqSize` Reflexivity & Top Element `#`)**:
    For every generic size variable `VGen k` and `#` (`VInfty`), `leqSize` succeeds. -/
theorem leqSize_infty (v : Val) (st : TCState) :
    runTypeCheck st (leqSize v .VInfty) = .ok ((), st) := rfl

theorem leqSize_gen_refl (k : Nat) (st : TCState) :
    runTypeCheck st (leqSize (.VGen k) (.VGen k)) = .ok ((), st) := by
  simp [leqSize, runTypeCheck]
  rfl

/-- **Theorem 4 (`leqSize` Unfolding Laws under `$`)** -/
theorem leqSize_succ_gen (k : Nat) (v2 : Val) :
    leqSize (.VGen k) (.VSucc v2) = leqSize (.VGen k) v2 := rfl

theorem leqSize_succ_both (v1 v2 : Val) :
    leqSize (.VSucc v1) (.VSucc v2) = leqSize v1 v2 := rfl

/-- **Theorem 5 (Size Erasure Invariance of `DotP` Matching)**:
    For any `.DotP e` pattern, `matchPat` never inspects whether the runtime value
    is a finite successor `.VSucc v` or erased `.VInfty` (`#`). -/
theorem matchPat_dotP_erased (fuel : Nat) (env : Env) (e : Expr) (v1 v2 : Val) (st : TCState) :
    runTypeCheck st (matchPat (fuel + 1) env (.DotP e) v1) =
    runTypeCheck st (matchPat (fuel + 1) env (.DotP e) v2) := rfl

/-- **Theorem 6 (Tightness of Bug 5 Fix — `SuccP` Breaks Runtime Size Erasure)**:
    If a clause were allowed to match on a successor size pattern `.SuccP (.VarP "i")`
    (which was permitted when `completeFun _ = True` in Mugda 2008), then matching against
    the un-erased size `.VSucc (.VGen 0)` binds `"i" ↦ .VGen 0`, whereas matching against
    its `#`-erasure `.VInfty` binds `"i" ↦ .VInfty`!
    This proves why `completePatterns` (`cp (.SuccP _) = false`) is necessary for size erasure. -/
theorem succP_breaks_size_erasure (st : TCState) :
    runTypeCheck st (matchPat 2 [] (.SuccP (.VarP "i")) (.VSucc (.VGen 0))) =
      .ok (some [("i", .VGen 0)], st) ∧
    runTypeCheck st (matchPat 2 [] (.SuccP (.VarP "i")) .VInfty) =
      .ok (some [("i", .VInfty)], st) ∧
    (some [("i", Val.VGen 0)] ≠ some [("i", Val.VInfty)]) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  injection h with hlist
  injection hlist with hhead _
  injection hhead with _ hv
  contradiction

/-! ## 2. Matrix Order `ORDER_+` Algebraic Laws & Bug 3 / Bug 4 Tightness (Pillar I & V) -/

/-- **Theorem 7 (Commutativity & Associativity of Scalar `Order` Operations)** -/
theorem minScalar_comm (a b : Order) : minScalar a b = minScalar b a := by
  cases a <;> cases b <;> rfl

theorem maxScalar_comm (a b : Order) : maxScalar a b = maxScalar b a := by
  cases a <;> cases b <;> rfl

theorem compScalar_assoc (a b c : Order) :
    compScalar (compScalar a b) c = compScalar a (compScalar b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **Theorem 8 (Bug 3b Fix — `maxO` on Two Matrices and `collapseOrder` Always Collapse to Scalars)**:
    Combining two `.Mat` values via `maxO` (or collapsing any `Order` via `collapseOrder`)
    can never produce a nested `.Mat m`. -/
theorem maxO_mat_never_mat (m1 m2 m : Matrix Order) :
    maxO (.Mat m1) (.Mat m2) ≠ .Mat m := by
  change maxScalar (collapseOrder (.Mat m1)) (collapseOrder (.Mat m2)) ≠ .Mat m
  unfold maxScalar
  split <;> intro h <;> injection h

theorem collapseOrder_never_mat (o : Order) (m : Matrix Order) :
    collapseOrder o ≠ .Mat m := by
  cases o with
  | Lt => intro h; injection h
  | Le => intro h; injection h
  | Un => intro h; injection h
  | Mat rows =>
    unfold collapseOrder
    cases rows with
    | nil => intro h; injection h
    | cons r rs =>
      cases rs with
      | nil =>
        unfold collapseRows
        cases r with
        | nil => intro h; injection h
        | cons o0 os =>
          unfold collapseElemAt
          exact collapseOrder_never_mat o0 m
      | cons r2 rs2 =>
        unfold collapseRows minScalar
        split <;> intro h <;> injection h

/-- **Theorem 9 (Bug 3a Fix — `isPurePat` Excludes `DotP` and `SuccP`)**:
    `isPurePat` returns `false` on `.DotP` and `.SuccP`, ensuring `compareExpr` never
    constructs a `Mat` matrix for sized constructors with dot-pattern size indices. -/
theorem isPurePat_dotP_false (e : Expr) : isPurePat (.DotP e) = false := rfl
theorem isPurePat_succP_false (p : Pattern) : isPurePat (.SuccP p) = false := rfl

/-- **Theorem 10 (Bug 4 Fix — `collectCallsExpr` Extracts Calls from `LLet` Bound Expressions)**:
    Every call extracted from `e1` is included in the calls extracted from `.LLet x t1 e1 e2`. -/
theorem collectCalls_llet_includes_bound
    (nl : List (Name × Nat)) (f : Name) (pl : List Pattern)
    (x : Name) (t1 e1 e2 : Expr) (c : Call)
    (hc : c ∈ collectCallsExpr nl f pl e1) :
    c ∈ collectCallsExpr nl f pl (.LLet x t1 e1 e2) := by
  unfold collectCallsExpr
  exact List.mem_append_left _ (List.mem_append_right _ hc)

/-! ## 3. End-to-End Positive Expressiveness & Counterexample Suite (`native_decide`) -/

section VerificationSuite

/-- `sized data SNat : Size -> Set { zero : (i : Size) -> SNat ($ i) ; succ : (i : Size) -> SNat i -> SNat ($ i) }` -/
def snatDecl : Declaration :=
  .DataDecl "SNat" .Sized .Ind [] [] (.Pi "i" .Size .Set)
    [ .mk "zero" (.Pi "i" .Size (.App (.Def "SNat") [.Succ (.Var "i")]))
    , .mk "succ" (.Pi "i" .Size (.Pi "" (.App (.Def "SNat") [.Var "i"]) (.App (.Def "SNat") [.Succ (.Var "i")])))
    ]

/-- `fun sub : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i` (Euclidean subtraction, `examples/snat.ma`) -/
def subDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "sub"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.Pi "j" .Size
               (.Pi "" (.App (.Def "SNat") [.Var "j"])
                 (.App (.Def "SNat") [.Var "i"])))))
     , [ .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "zero" [.VarP "i"], .VarP "j", .VarP "y"]
             (.App (.Con .Ind "zero") [.Var "i"])
       , .mk [.VarP "i", .VarP "x", .DotP (.Succ (.Var "j")), .ConP .Ind "zero" [.VarP "j"]]
             (.Var "x")
       , .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "succ" [.VarP "i", .VarP "x"],
              .DotP (.Succ (.Var "j")), .ConP .Ind "succ" [.VarP "j", .VarP "y"]]
             (.App (.Def "sub") [.Succ (.Var "i"), .Var "x", .Var "j", .Var "y"])
       ]
     )]

/-- Counterexample `snat_mat_bug.ma` (Bugs 1 & 3):
    `fun loop : (i : Size) -> SNat i -> SNat i -> SNat #` -/
def snatMatBugDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "loop"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.Pi "" (.App (.Def "SNat") [.Var "i"])
               (.App (.Def "SNat") [.Infty]))))
     , [ .mk [ .DotP (.Succ (.Succ (.Succ (.Var "i"))))
             , .ConP .Ind "succ" [.DotP (.Succ (.Succ (.Var "i"))),
                 .ConP .Ind "succ" [.DotP (.Succ (.Var "i")),
                   .ConP .Ind "succ" [.VarP "i", .VarP "z"]]]
             , .ConP .Ind "succ" [.DotP (.Succ (.Succ (.Var "i"))),
                 .ConP .Ind "succ" [.DotP (.Succ (.Var "i")), .VarP "w"]]
             ]
             (.App (.Def "loop")
               [ .Succ (.Succ (.Succ (.Var "i")))
               , .App (.Con .Ind "succ") [.Succ (.Var "i"), .Var "w"]
               , .App (.Con .Ind "succ") [.Succ (.Succ (.Var "i")),
                   .App (.Con .Ind "succ") [.Succ (.Var "i"), .Var "w"]]
               ])
       ]
     )]

/-- **Verified Test 1 (Positive Adequacy — `SNat` + `sub`)** -/
theorem snat_and_sub_accepted :
    (checkProgram [snatDecl, subDecl]).isOk = true := by native_decide

/-- **Verified Test 2 (Counterexample Rejection — Bug 1 & Bug 3 `snat_mat_bug.ma`)** -/
theorem snat_mat_bug_rejected :
    (checkProgram [snatDecl, snatMatBugDecl]).isOk = false := by native_decide

/-- `sized data Wrap (+ A : Set) : Size -> Set { wrap : (i : Size) -> A -> Wrap A ($ i) }` -/
def wrapDecl : Declaration :=
  .DataDecl "Wrap" .Sized .Ind [.SPos] [("A", .Set)] (.Pi "i" .Size .Set)
    [ .mk "wrap" (.Pi "i" .Size (.Pi "" (.Var "A") (.App (.Def "Wrap") [.Var "A", .Succ (.Var "i")]))) ]

/-- Counterexample `loop_wrapped.ma` (Bugs 1 & 2) -/
def badWrapFunDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "badWrap"
         (.Pi "j" .Size
           (.Pi "" (.App (.Def "Wrap") [.Pi "" (.App (.Def "SNat") [.Var "j"]) (.App (.Def "SNat") [.Infty]), .Var "j"])
             (.Pi "" (.App (.Def "SNat") [.Var "j"])
               (.App (.Def "SNat") [.Infty]))))
     , [ .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "wrap" [.VarP "i", .VarP "f"], .VarP "x"]
             (.App (.Var "f") [.Var "x"])
       ]
     )]

/-- **Verified Test 3 (Counterexample Rejection — Bug 1 & Bug 2 `Wrap` Parameter Smuggling)** -/
theorem loop_wrapped_rejected :
    (checkProgram [snatDecl, wrapDecl, badWrapFunDecl]).isOk = false := by native_decide

/-- Counterexample `llet_bug.ma` (Bug 4 — recursive call hidden inside a local `let` binding) -/
def lletBugDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "loopLet"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.App (.Def "SNat") [.Infty])))
     , [ .mk [.VarP "i", .VarP "x"]
             (.LLet "y" (.App (.Def "SNat") [.Infty])
               (.App (.Def "loopLet") [.Var "i", .Var "x"])
               (.Var "y"))
       ]
     )]

/-- **Verified Test 4 (Counterexample Rejection — Bug 4 `LLet` Call Extraction)** -/
theorem llet_bug_rejected :
    (checkProgram [snatDecl, lletBugDecl]).isOk = false := by native_decide

/-- **Verified Test 5 (End-to-End `.ma` Source — Euclidean Division `div` in `examples/snat.ma`)** -/
def snatDivSource : String := "
sized data SNat : Size -> Set
{ zero : (i : Size) -> SNat ($ i)
; succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun sub : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ sub .($ i) (zero i) j y = zero i
; sub i x .($ j) (zero j) = x
; sub .($ i) (succ i x) .($ j) (succ j y) = sub ($ i) x j y
}

fun div : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ div .($ i) (zero i) j y = zero i
; div .($ i) (succ i x) j y = succ i (div i (sub i x j y) j y)
}
"

theorem snat_div_source_accepted :
    (checkSource snatDivSource).isOk = true := by native_decide

/-- **Verified Test 6 (End-to-End `.ma` Source Rejection — Cody Roux's `cody_nowraps.ma`)** -/
def codyNoWrapsSource : String := "
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

fun loop : (i : Size) -> O i -> O i -> Nat
{ loop .($ ($ ($ i)))
       (M .($ ($ i)) (L .($ i) g) (Z .($ i)))
       (M .($ ($ i)) (L .($ i) f) (S .($ i) (S i z)))
  = loop ($ ($ i))
         (M ($ i) (L i g) (Z i))
         (M ($ i) (g zero) (f zero))
; loop i x y = zero
}
"

theorem cody_nowraps_source_rejected :
    (checkSource codyNoWrapsSource).isOk = false := by native_decide

/-- **Verified Test 7 (End-to-End Coinductive Fibonacci Stream & Evaluation — `examples/fib.ma`)** -/
def fibSource : String := "
data Nat : Set {
  zero : Nat;
  succ : Nat -> Nat
}

fun add : Nat -> Nat -> Nat {
  add zero = \\y -> y;
  add (succ x) = \\y -> succ (add x y)
}

sized codata Stream : Size -> Set {
  cons : (i : Size) -> Nat -> Stream i -> Stream ($ i)
}

fun tail : Stream # -> Stream # {
  tail (cons .# x xs) = xs
}

fun head : Stream # -> Nat {
  head (cons .# x xs) = x
}

fun nth : Nat -> Stream # -> Nat {
  nth zero xs = head xs;
  nth (succ x) xs = nth x (tail xs)
}

let 1 : Nat = (succ zero)

cofun fib' : (x : Nat) -> (y : Nat) -> (i : Size) -> Stream i {
  fib' x y ($ i) = cons i x (fib' y (add x y) i)
}

let fib : Stream # = (fib' 1 1 #)
let 4 : Nat = (succ (succ (succ 1)))
eval let fib4 : Nat = nth 4 fib
"

theorem fib_source_evaluates_to_5 :
    (evalSource fibSource).toOption =
    some ["fib4 evaluates to (succ (succ (succ (succ (succ zero)))))"] := by native_decide

/-- **Verified Test 8 (End-to-End `ORDER_+` Matrix Termination — `addpair` and `ack` in `examples/natpair.ma`)** -/
def natpairSource : String := "
data Nat : Set {
  zero : Nat;
  succ : Nat -> Nat
}

data NatPair : Set {
  Pair : Nat -> Nat -> NatPair
}

fun addpair : NatPair -> Nat {
  addpair (Pair x zero) = x;
  addpair (Pair x (succ y)) = succ (addpair (Pair x y))
}

fun ack : NatPair -> Nat {
  ack (Pair zero y) = succ y;
  ack (Pair (succ x) zero) = ack (Pair x (succ zero));
  ack (Pair (succ x) (succ y)) = ack (Pair x (ack (Pair (succ x) y)))
}
"

theorem natpair_source_accepted :
    (checkSource natpairSource).isOk = true := by native_decide

end VerificationSuite

end MugdaCore
