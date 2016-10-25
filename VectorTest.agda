module VectorTest where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 20 _::_

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: x₁) = suc (length x₁)

refine : {A : Set} {n : Nat} (xs : List A) -> Vec A (length xs)
refine [] = []
refine (x :: x₁) = x :: refine x₁


data _==_  {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

test-list : List Nat
test-list = 1 :: 0 :: []

test-vec : Vec Nat 2
test-vec = refine test-list

promote-works : refine test-list == (1 :: 0 :: [])
promote-works = refl
