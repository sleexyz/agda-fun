module VectorTest where

data _==_  {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}


cong : ∀{l} {A B : Set l} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
cong _ refl = refl

subst : ∀{l} {A : Set l} {x y : A} (P : A -> Set l) -> x == y -> P x -> P y
subst _ refl x = x



data Nat : Set where
  zero : Nat
  succ  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

infixl 9 _+_
_+_ : Nat -> Nat -> Nat
zero + y = y
succ x + y = succ (x + y)

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

infixr 20 _::_

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: x₁) = succ (length x₁)

refine : {A : Set} (xs : List A) -> Vec A (length xs)
refine [] = []
refine (x :: x₁) = x :: refine x₁

refine-works-example : refine (1 :: 0 :: []) == (1 :: 0 :: [])
refine-works-example = refl

-- | Vector concat
_++_ : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


plus-zero : (x : Nat) -> (x + 0) == x
plus-zero zero = refl
-- plus-zero (succ x) rewrite (plus-zero x)= refl
plus-zero (succ x) = cong succ (plus-zero x)

plus-succ : (n : Nat) -> (m : Nat) -> (n + succ m) == (succ n + m)
plus-succ zero m = refl
-- plus-succ (succ n) m rewrite (plus-succ n m) = refl
plus-succ (succ n) m = cong succ (plus-succ n m)

reverseVecAux : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
reverseVecAux [] ys = ys
reverseVecAux {a} {succ n} {m} (x :: xs) ys = subst (Vec _) (plus-succ n m) (reverseVecAux xs (x :: ys))

reverseVec : {A : Set} {n : Nat} -> Vec A n -> Vec A n
reverseVec {_} {n} v = subst (Vec _) (plus-zero n) (reverseVecAux v [])
