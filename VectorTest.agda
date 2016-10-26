module VectorTest where

data _==_  {a} {A : Set a} (x : A) : A -> Set a where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}


cong : ∀{l} {A B : Set l} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
cong f refl = refl

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

refine : {A : Set} {n : Nat} (xs : List A) -> Vec A (length xs)
refine [] = []
refine (x :: x₁) = x :: refine x₁

promote-works-example : refine (1 :: 0 :: []) == (1 :: 0 :: [])
promote-works-example = refl

-- | Vector concat
_++_ : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- | Vector reverse
reverseVec : {A : Set} {n : Nat} -> Vec A n -> Vec A n
reverseVec v = {!!}

plus-zero : (x : Nat) -> x == (x + 0)
plus-zero zero = refl
plus-zero (succ x) = cong succ (plus-zero x)

reverseVecAux : {A : Set} {n m : Nat} -> Vec A n -> Vec A m ->  Vec A (n + m)
reverseVecAux [] ys = ys
reverseVecAux (x :: xs) ys = {!!} reverseVecAux xs (x :: ys)

