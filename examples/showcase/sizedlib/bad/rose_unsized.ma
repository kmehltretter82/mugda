-- Expect: reject (Termination check fails: rose tree flattening without sizes)
--
-- flatten of sizedlib (src/02_sized.ma) on an unsized rose tree.  The
-- recursive call is passed, partially applied, to `map`, so the checker
-- never sees it applied to a subtree.  In sizedlib, the subtrees have
-- type `Rose A i` inside a node of type `Rose A ($ i)`, so the partial
-- application `flatten A i` is already at a smaller size.

data List (+ A : Set) : Set
{
  nil  : List A;
  cons : A -> List A -> List A
}

fun append : (A : Set) -> List A -> List A -> List A
{
  append .A (nil A)       ys = ys;
  append .A (cons A x xs) ys = cons A x (append A xs ys)
}

fun map : (A : Set) -> (B : Set) -> (A -> B) -> List A -> List B
{
  map .A B f (nil A)       = nil B;
  map .A B f (cons A x xs) = cons B (f x) (map A B f xs)
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

fun flatten : (A : Set) -> Rose A -> List A
{
  flatten .A (rose A a ts) = cons A a (concat A (map (Rose A) (List A) (flatten A) ts))
}
