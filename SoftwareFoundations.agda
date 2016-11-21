module SoftwareFoundations where

data Bool : Set where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

infix 7 -_

-_ : Bool -> Bool
- true = false
- false = true

infixl 6 _&&_
_&&_ : Bool -> Bool -> Bool
true && true = true
_ && _ = false


infixl 5  _||_
_||_ : Bool -> Bool -> Bool
false || false = false
_ || _ = true


infixl -60 _≡_

data _≡_ {l} {A : Set l} (x : A) : A → Set l where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

test_||1 : true || false ≡ true
test_||1 = refl
test_||2 : false || false ≡ false
test_||2 = refl
test_||3 : false || true ≡ true
test_||3 = refl
test_||4 : true || true ≡ true
test_||4 = refl


nand : Bool -> Bool -> Bool
nand x y = - (x && y)

test_nand1 : nand true false ≡ true
test_nand1 = refl

