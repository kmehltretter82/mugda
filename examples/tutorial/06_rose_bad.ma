-- Tutorial chapter 6: Higher-order and nested data
-- Expect: reject (termination)
-- Flattening an unsized rose tree. The data type is fine (List's parameter
-- is `+`), but `flat` passes the partial application `flat A` to `mapL`.
-- The checker fills in the missing argument with "?" (unknown), so the
-- call matrix has no decrease, and the termination check fails. In
-- 06_higher_order.ma the size argument `i` decreases even in the partial
-- application, which is why the sized version is accepted.

data List (+ A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

fun mapL : (A : Set) -> (B : Set) -> (A -> B) -> List A -> List B
{
  mapL .A B f (nil A)       = nil B;
  mapL .A B f (cons A x xs) = cons B (f x) (mapL A B f xs)
}

fun append : (A : Set) -> List A -> List A -> List A
{
  append .A (nil A)       ys = ys;
  append .A (cons A x xs) ys = cons A x (append A xs ys)
}

fun concat : (A : Set) -> List (List A) -> List A
{
  concat A (nil .(List A))       = nil A;
  concat A (cons .(List A) l ls) = append A l (concat A ls)
}

data Rose (+ A : Set) : Set
{
  rose : A -> List (Rose A) -> Rose A
}

fun flat : (A : Set) -> Rose A -> List A
{
  flat .A (rose A a rs) = cons A a (concat A (mapL (Rose A) (List A) (flat A) rs))
}
