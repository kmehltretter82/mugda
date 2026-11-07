# Chapter 1 — First Steps: Explicit Dependent Types

**Companion files:**
- Accepted: [`examples/tutorial/01_first_steps.ma`](../examples/tutorial/01_first_steps.ma)
- Rejected: [`examples/tutorial/01_first_steps_bad.ma`](../examples/tutorial/01_first_steps_bad.ma)
- Solutions: [`examples/tutorial/solutions/sol_01_bool_nat.ma`](../examples/tutorial/solutions/sol_01_bool_nat.ma)

---

## 1. Design Philosophy: Everything Is Explicit

Mugda is a small, self-contained core language for dependent pattern matching with sized types and size-change termination. To keep its metatheory and typechecker completely transparent:

1. **No module imports:** Every `.ma` file is self-contained (or concatenated from parts by `make`).
2. **No implicit arguments:** Type parameters (`A : Set`) and size indices (`i : Size`) are always passed explicitly both in expressions and in constructor patterns.
3. **Inaccessible (dot) patterns `.t`:** When an argument on the left-hand side of a clause is forced by typing (such as a type parameter `.A` or an index `.(succ n)`), you prefix it with a dot `.`.

---

## 2. Inductive Data Types (`data`) and Functions (`fun`)

From [`01_first_steps.ma`](../examples/tutorial/01_first_steps.ma):

```mugda
data Bool : Set {
  tt : Bool ;
  ff : Bool
}

data Nat : Set {
  zero : Nat ;
  succ : Nat -> Nat
}

fun not : Bool -> Bool {
  not tt = ff ;
  not ff = tt
}

fun add : Nat -> Nat -> Nat {
  add zero     y = y ;
  add (succ x) y = succ (add x y)
}
```

### Polymorphic Functions & Parameterized Data Types

When a `data` type has parameters like `(A : Set)`, its constructors take `A` as their first argument. In pattern matching, the parameter in a constructor pattern (`nil A` or `cons A x xs`) is bound inside the constructor pattern, while the outer function's type argument is marked as a dot pattern `.A`:

```mugda
data List (A : Set) : Set {
  nil  : List A ;
  cons : A -> List A -> List A
}

fun length : (A : Set) -> List A -> Nat {
  length .A (nil A)       = zero ;
  length .A (cons A x xs) = succ (length A xs)
}
```

### Equational Proofs (`Eq` and `refl`)

Inductive families place indices *after* the colon `:`:

```mugda
data Eq (A : Set) : A -> A -> Set {
  refl : (a : A) -> Eq A a a
}

fun zeroRight : (x : Nat) -> Eq Nat (add x zero) x {
  zeroRight zero     = refl Nat zero ;
  zeroRight (succ x) = cong (add x zero) x (zeroRight x)
}
```

---

## 3. Running the Checker & Reading Output

Run:

```bash
.lake/build/bin/mugda examples/tutorial/01_first_steps.ma
```

Output:

```text
***** Mugda v1.0 (Constructive Lean 4 Edition) *****
--- scope checking ---
--- type checking ---
--- evaluating ---
six evaluates to (succ (succ (succ (succ (succ (succ zero))))))
five evaluates to (succ (succ (succ (succ (succ zero)))))
four evaluates to (succ (succ (succ (succ zero))))
bools evaluates to (cons Bool tt (cons Bool ff (cons Bool tt (nil Bool))))
len evaluates to (succ (succ (succ zero)))
```

Every `eval let name : Type = expr` declaration is normalized after typechecking and printed as `name evaluates to ...`.

By contrast, [`01_first_steps_bad.ma`](../examples/tutorial/01_first_steps_bad.ma) passes `zero : Nat` to `not : Bool -> Bool` and is immediately rejected with exit code `1`:

```text
error during typechecking:
bad: eqVal error
```

---

## 4. Exercises

1. Write `xor : Bool -> Bool -> Bool` and evaluate `xor tt ff`.
2. Write exponentiation `exp : Nat -> Nat -> Nat` (`exp b e = b^e`) using `mul` and evaluate `exp 2 3`.

Compare your answers with [`examples/tutorial/solutions/sol_01_bool_nat.ma`](../examples/tutorial/solutions/sol_01_bool_nat.ma).
