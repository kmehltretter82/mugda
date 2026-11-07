
----------------------------------------------------------------------
-- Part 4: A verified compiler
--
-- Source:  arithmetic expressions with constants, +, * and if-zero.
-- Target:  a stack machine.  Code is a list of instructions; the
--          if-zero instruction carries its two branches as nested code
--          (structured control flow instead of jumps).
--
-- Theorem (compile_correct):
--   exec (compile e ++ c) s  ==  exec c (evalE e :: s)
--
-- Everything is proved in full -- nothing had to be dropped.  Two design
-- choices make this possible in Mugda:
--   * Structured branches (`ibranch then else`) instead of jump offsets.
--     With jumps, exec would need fuel or well-founded recursion, and the
--     proof would need arithmetic on code addresses.
--   * `exec (i :: c) s = exec c (step i s)`.  This makes the key lemma
--     exec (c1 ++ c2) s = exec c2 (exec c1 s) a one-line induction that
--     never inspects the instruction.
-- Stack underflow is not ruled out by types (we use an untyped stack and
-- let a binary operation on a too-short stack leave it unchanged); the
-- theorem shows that compiled code never underflows.
--
-- The termination checker accepts all of this structurally (no sizes
-- needed): exec and step are mutually recursive and the nested code of
-- `ibranch t e` is a subterm of the instruction list.
----------------------------------------------------------------------

data Expr : Set
{
  lit   : Nat -> Expr;
  plus  : Expr -> Expr -> Expr;
  times : Expr -> Expr -> Expr;
  ifz   : Expr -> Expr -> Expr -> Expr      -- if-zero c then t else e
}

fun ifzero : (A : Set) -> Nat -> A -> A -> A
{
  ifzero A zero     a b = a;
  ifzero A (succ n) a b = b
}

-- the denotational semantics
fun evalE : Expr -> Nat
{
  evalE (lit n)     = n;
  evalE (plus a b)  = add (evalE a) (evalE b);
  evalE (times a b) = mul (evalE a) (evalE b);
  evalE (ifz c t e) = ifzero Nat (evalE c) (evalE t) (evalE e)
}

data Instr : Set
{
  ipush   : Nat -> Instr;
  iadd    : Instr;
  imul    : Instr;
  ibranch : List Instr -> List Instr -> Instr  -- pop n; run first code if n = 0
}

let Code  : Set = List Instr
let Stack : Set = List Nat

-- pop y, pop x, push (f x y)
fun binop : (Nat -> Nat -> Nat) -> Stack -> Stack
{
  binop f (nil .Nat)                    = nil Nat;
  binop f (cons .Nat y (nil .Nat))      = cons Nat y (nil Nat);
  binop f (cons .Nat y (cons .Nat x s)) = cons Nat (f x y) s
}

-- pop n, then continue with f (n = 0) or g (n > 0)
fun branch : (Stack -> Stack) -> (Stack -> Stack) -> Stack -> Stack
{
  branch f g (nil .Nat)             = nil Nat;
  branch f g (cons .Nat zero s)     = f s;
  branch f g (cons .Nat (succ n) s) = g s
}

mutual
{
  fun exec : Code -> Stack -> Stack
  {
    exec (nil .Instr)      s = s;
    exec (cons .Instr i c) s = exec c (step i s)
  }

  fun step : Instr -> Stack -> Stack
  {
    step (ipush n)     s = cons Nat n s;
    step iadd          s = binop add s;
    step imul          s = binop mul s;
    step (ibranch t e) s = branch (exec t) (exec e) s
  }
}

let single : Instr -> Code = \ i -> cons Instr i (nil Instr)

fun compile : Expr -> Code
{
  compile (lit n)     = single (ipush n);
  compile (plus a b)  = append Instr (compile a) (append Instr (compile b) (single iadd));
  compile (times a b) = append Instr (compile a) (append Instr (compile b) (single imul));
  compile (ifz c t e) = append Instr (compile c) (single (ibranch (compile t) (compile e)))
}

----------------------------------------------------------------------
-- Correctness proof
----------------------------------------------------------------------

-- Running concatenated code = running the parts one after the other.
fun exec_append : (c1 : Code) -> (c2 : Code) -> (s : Stack) ->
  Eq Stack (exec (append Instr c1 c2) s) (exec c2 (exec c1 s))
{
  exec_append (nil .Instr)      c2 s = refl Stack (exec c2 s);
  exec_append (cons .Instr i c1) c2 s = exec_append c1 c2 (step i s)
}

-- Two sub-computations in sequence, followed by code k.  Used for both
-- binary operators.
fun seq2 : (ca : Code) -> (cb : Code) -> (k : Code) -> (va : Nat) -> (vb : Nat) ->
  (s : Stack) ->
  Eq Stack (exec ca s) (cons Nat va s) ->
  Eq Stack (exec cb (cons Nat va s)) (cons Nat vb (cons Nat va s)) ->
  Eq Stack (exec (append Instr ca (append Instr cb k)) s)
           (exec k (cons Nat vb (cons Nat va s)))
{
  seq2 ca cb k va vb s pa pb =
    trans Stack
      (exec (append Instr ca (append Instr cb k)) s)
      (exec (append Instr cb k) (exec ca s))
      (exec k (cons Nat vb (cons Nat va s)))
      (exec_append ca (append Instr cb k) s)
      (trans Stack
        (exec (append Instr cb k) (exec ca s))
        (exec (append Instr cb k) (cons Nat va s))
        (exec k (cons Nat vb (cons Nat va s)))
        (cong Stack Stack (exec (append Instr cb k)) (exec ca s) (cons Nat va s) pa)
        (trans Stack
          (exec (append Instr cb k) (cons Nat va s))
          (exec k (exec cb (cons Nat va s)))
          (exec k (cons Nat vb (cons Nat va s)))
          (exec_append cb k (cons Nat va s))
          (cong Stack Stack (exec k) (exec cb (cons Nat va s))
                (cons Nat vb (cons Nat va s)) pb)))
}

-- The branch instruction does the right thing, by case analysis on the
-- popped value.  (Mugda has no `with`; the case split is a helper
-- function that matches on n.)
fun branch_ok : (ct : Code) -> (ce : Code) -> (vt : Nat) -> (ve : Nat) -> (s : Stack) ->
  Eq Stack (exec ct s) (cons Nat vt s) ->
  Eq Stack (exec ce s) (cons Nat ve s) ->
  (n : Nat) ->
  Eq Stack (branch (exec ct) (exec ce) (cons Nat n s)) (cons Nat (ifzero Nat n vt ve) s)
{
  branch_ok ct ce vt ve s pt pe zero     = pt;
  branch_ok ct ce vt ve s pt pe (succ n) = pe
}

-- Compiled code pushes the value of the expression.
fun correct : (e : Expr) -> (s : Stack) ->
  Eq Stack (exec (compile e) s) (cons Nat (evalE e) s)
{
  correct (lit n) s = refl Stack (cons Nat n s);
  correct (plus a b) s =
    seq2 (compile a) (compile b) (single iadd) (evalE a) (evalE b) s
         (correct a s) (correct b (cons Nat (evalE a) s));
  correct (times a b) s =
    seq2 (compile a) (compile b) (single imul) (evalE a) (evalE b) s
         (correct a s) (correct b (cons Nat (evalE a) s));
  correct (ifz c t e) s =
    let k : Code = single (ibranch (compile t) (compile e)) in
    trans Stack
      (exec (append Instr (compile c) k) s)
      (exec k (exec (compile c) s))
      (cons Nat (ifzero Nat (evalE c) (evalE t) (evalE e)) s)
      (exec_append (compile c) k s)
      (trans Stack
        (exec k (exec (compile c) s))
        (exec k (cons Nat (evalE c) s))
        (cons Nat (ifzero Nat (evalE c) (evalE t) (evalE e)) s)
        (cong Stack Stack (exec k) (exec (compile c) s) (cons Nat (evalE c) s) (correct c s))
        (branch_ok (compile t) (compile e) (evalE t) (evalE e) s
                   (correct t s) (correct e s) (evalE c)))
}

-- The main theorem: exec (compile e ++ c) s == exec c (evalE e :: s)
fun compile_correct : (e : Expr) -> (c : Code) -> (s : Stack) ->
  Eq Stack (exec (append Instr (compile e) c) s) (exec c (cons Nat (evalE e) s))
{
  compile_correct e c s =
    trans Stack
      (exec (append Instr (compile e) c) s)
      (exec c (exec (compile e) s))
      (exec c (cons Nat (evalE e) s))
      (exec_append (compile e) c s)
      (cong Stack Stack (exec c) (exec (compile e) s) (cons Nat (evalE e) s) (correct e s))
}

----------------------------------------------------------------------
-- A verified optimisation pass: constant folding.
-- To avoid overlapping clauses (see Part 2), the "smart constructors"
-- match on every constructor of the first argument.
----------------------------------------------------------------------

fun foldPlus : Expr -> Expr -> Expr
{
  foldPlus (lit n)     (lit m)     = lit (add n m);
  foldPlus (lit n)     (plus c d)  = plus (lit n) (plus c d);
  foldPlus (lit n)     (times c d) = plus (lit n) (times c d);
  foldPlus (lit n)     (ifz c d f) = plus (lit n) (ifz c d f);
  foldPlus (plus a b)  y           = plus (plus a b) y;
  foldPlus (times a b) y           = plus (times a b) y;
  foldPlus (ifz a b c) y           = plus (ifz a b c) y
}

fun foldTimes : Expr -> Expr -> Expr
{
  foldTimes (lit n)     (lit m)     = lit (mul n m);
  foldTimes (lit n)     (plus c d)  = times (lit n) (plus c d);
  foldTimes (lit n)     (times c d) = times (lit n) (times c d);
  foldTimes (lit n)     (ifz c d f) = times (lit n) (ifz c d f);
  foldTimes (plus a b)  y           = times (plus a b) y;
  foldTimes (times a b) y           = times (times a b) y;
  foldTimes (ifz a b c) y           = times (ifz a b c) y
}

-- if-zero with a known condition picks its branch at compile time
fun foldIfz : Expr -> Expr -> Expr -> Expr
{
  foldIfz (lit zero)     t e = t;
  foldIfz (lit (succ n)) t e = e;
  foldIfz (plus a b)     t e = ifz (plus a b) t e;
  foldIfz (times a b)    t e = ifz (times a b) t e;
  foldIfz (ifz a b c)    t e = ifz (ifz a b c) t e
}

fun cfold : Expr -> Expr
{
  cfold (lit n)     = lit n;
  cfold (plus a b)  = foldPlus (cfold a) (cfold b);
  cfold (times a b) = foldTimes (cfold a) (cfold b);
  cfold (ifz c t e) = foldIfz (cfold c) (cfold t) (cfold e)
}

-- Each smart constructor is correct, by computation in every case.
fun foldPlus_ok : (x : Expr) -> (y : Expr) ->
  Eq Nat (evalE (foldPlus x y)) (add (evalE x) (evalE y))
{
  foldPlus_ok (lit n)     (lit m)     = refl Nat (add n m);
  foldPlus_ok (lit n)     (plus c d)  = refl Nat (add n (add (evalE c) (evalE d)));
  foldPlus_ok (lit n)     (times c d) = refl Nat (add n (mul (evalE c) (evalE d)));
  foldPlus_ok (lit n)     (ifz c d f) = refl Nat (add n (evalE (ifz c d f)));
  foldPlus_ok (plus a b)  y           = refl Nat (add (evalE (plus a b)) (evalE y));
  foldPlus_ok (times a b) y           = refl Nat (add (evalE (times a b)) (evalE y));
  foldPlus_ok (ifz a b c) y           = refl Nat (add (evalE (ifz a b c)) (evalE y))
}

fun foldTimes_ok : (x : Expr) -> (y : Expr) ->
  Eq Nat (evalE (foldTimes x y)) (mul (evalE x) (evalE y))
{
  foldTimes_ok (lit n)     (lit m)     = refl Nat (mul n m);
  foldTimes_ok (lit n)     (plus c d)  = refl Nat (mul n (add (evalE c) (evalE d)));
  foldTimes_ok (lit n)     (times c d) = refl Nat (mul n (mul (evalE c) (evalE d)));
  foldTimes_ok (lit n)     (ifz c d f) = refl Nat (mul n (evalE (ifz c d f)));
  foldTimes_ok (plus a b)  y           = refl Nat (mul (evalE (plus a b)) (evalE y));
  foldTimes_ok (times a b) y           = refl Nat (mul (evalE (times a b)) (evalE y));
  foldTimes_ok (ifz a b c) y           = refl Nat (mul (evalE (ifz a b c)) (evalE y))
}

fun foldIfz_ok : (c : Expr) -> (t : Expr) -> (e : Expr) ->
  Eq Nat (evalE (foldIfz c t e)) (ifzero Nat (evalE c) (evalE t) (evalE e))
{
  foldIfz_ok (lit zero)     t e = refl Nat (evalE t);
  foldIfz_ok (lit (succ n)) t e = refl Nat (evalE e);
  foldIfz_ok (plus a b)     t e = refl Nat (evalE (ifz (plus a b) t e));
  foldIfz_ok (times a b)    t e = refl Nat (evalE (ifz (times a b) t e));
  foldIfz_ok (ifz a b c)    t e = refl Nat (evalE (ifz (ifz a b c) t e))
}

-- congruence for two and three arguments
fun cong2 : (A : Set) -> (B : Set) -> (C : Set) -> (f : A -> B -> C) ->
  (a : A) -> (a' : A) -> (b : B) -> (b' : B) ->
  Eq A a a' -> Eq B b b' -> Eq C (f a b) (f a' b')
{
  cong2 .A .B C f .a .a .b .b (refl A a) (refl B b) = refl C (f a b)
}

fun cong3 : (A : Set) -> (B : Set) -> (C : Set) -> (D : Set) -> (f : A -> B -> C -> D) ->
  (a : A) -> (a' : A) -> (b : B) -> (b' : B) -> (c : C) -> (c' : C) ->
  Eq A a a' -> Eq B b b' -> Eq C c c' -> Eq D (f a b c) (f a' b' c')
{
  cong3 .A .B .C D f .a .a .b .b .c .c (refl A a) (refl B b) (refl C c) = refl D (f a b c)
}

-- constant folding preserves the meaning of every expression
fun cfold_ok : (e : Expr) -> Eq Nat (evalE (cfold e)) (evalE e)
{
  cfold_ok (lit n) = refl Nat n;
  cfold_ok (plus a b) =
    trans Nat (evalE (foldPlus (cfold a) (cfold b)))
              (add (evalE (cfold a)) (evalE (cfold b)))
              (add (evalE a) (evalE b))
      (foldPlus_ok (cfold a) (cfold b))
      (cong2 Nat Nat Nat add (evalE (cfold a)) (evalE a) (evalE (cfold b)) (evalE b)
             (cfold_ok a) (cfold_ok b));
  cfold_ok (times a b) =
    trans Nat (evalE (foldTimes (cfold a) (cfold b)))
              (mul (evalE (cfold a)) (evalE (cfold b)))
              (mul (evalE a) (evalE b))
      (foldTimes_ok (cfold a) (cfold b))
      (cong2 Nat Nat Nat mul (evalE (cfold a)) (evalE a) (evalE (cfold b)) (evalE b)
             (cfold_ok a) (cfold_ok b));
  cfold_ok (ifz c t e) =
    trans Nat (evalE (foldIfz (cfold c) (cfold t) (cfold e)))
              (ifzero Nat (evalE (cfold c)) (evalE (cfold t)) (evalE (cfold e)))
              (ifzero Nat (evalE c) (evalE t) (evalE e))
      (foldIfz_ok (cfold c) (cfold t) (cfold e))
      (cong3 Nat Nat Nat Nat (ifzero Nat)
             (evalE (cfold c)) (evalE c) (evalE (cfold t)) (evalE t)
             (evalE (cfold e)) (evalE e)
             (cfold_ok c) (cfold_ok t) (cfold_ok e))
}

-- The optimising compiler is correct, too.
fun optimised_correct : (e : Expr) -> (s : Stack) ->
  Eq Stack (exec (compile (cfold e)) s) (cons Nat (evalE e) s)
{
  optimised_correct e s =
    trans Stack
      (exec (compile (cfold e)) s)
      (cons Nat (evalE (cfold e)) s)
      (cons Nat (evalE e) s)
      (correct (cfold e) s)
      (cong Nat Stack (\ v -> cons Nat v s) (evalE (cfold e)) (evalE e) (cfold_ok e))
}

----------------------------------------------------------------------
-- Running the compiler
----------------------------------------------------------------------

-- (2 + 3) * (if-zero (1 * 0) then 4 else 9)  =  5 * 4  =  20
let prog : Expr =
  times (plus (lit n2) (lit n3))
        (ifz (times (lit n1) (lit n0)) (lit n4) (lit n9))

let empty : Stack = nil Nat

eval let prog_value    : Dec       = toDec (evalE prog)
eval let prog_code     : Code      = compile prog
eval let prog_run      : List Dec  = decs (exec (compile prog) empty)
eval let prog_folded   : Expr      = cfold prog
eval let prog_opt_code : Code      = compile (cfold prog)

-- instances of the theorems; a proof of a closed equation normalises to refl
eval let prog_ok : Eq Stack (exec (compile prog) empty) (cons Nat (evalE prog) empty)
  = correct prog empty
eval let prog_opt_ok : Eq Stack (exec (compile (cfold prog)) empty) (cons Nat (evalE prog) empty)
  = optimised_correct prog empty
