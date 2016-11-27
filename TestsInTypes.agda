module TestsInTypes where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product using (_×_; _,_)
open import Data.List
open import Data.Unit
open import Level

infix 4 _shouldBe_
_shouldBe_ = _≡_



test₁ :
    (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
  × (((1 ∷ 2 ∷ []) ++ (3 ∷ [])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
  × (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
test₁ =
    refl
  , refl
  , refl


data Hlist {n} : (xs : List (Set n)) → Set n where
  [] : Hlist []
  _∷_ : {x : Set n} {xs : List (Set n)} → x → Hlist xs → Hlist (x ∷ xs)

-- check : {xs : List Set} → Test (map (λ x → x ≡ x) xs)
-- check {a ∷ rest} = refl ∷ check {rest}
-- check {[]} = []


-- data Test {n} : (xs : List (Set (suc n))) → Set (suc n) where
--   [] : Test []
--   _∷_ : {x : Set n} {xs : List (Set (suc n))} → x ≡ x → Test xs → Test ((x ≡ x) ∷ xs)

-- data Test : (list : List Set) (xs : Hlist list) → Set1 where
--   [] : Test [] []
--   _∷_ : {A : Set} {x : A} {list : List Set} {xs : Hlist list} → x ≡ x → Test list xs → Test (A ∷ list) (x ∷ xs)

-- check : {list : List Set} {xs : Hlist list} → Test list xs
-- check {a ∷ list} {x ∷ rest} = refl ∷ check {list} {rest}
-- check {[]} {[]} = []

data Test {n} : {list : List (Set n)} (xs : Hlist list) → Set (suc n) where
  [] : Test []
  _∷_ : {A : Set n} {x : A} {list : List (Set n)} {xs : Hlist list} → x ≡ x → Test {n} {list} xs → Test {n} {A ∷ list} (x ∷ xs)

check : ∀{n} {list : List (Set n)} {xs : Hlist list} → Test {n} {list} xs
check {_} {a ∷ list} {x ∷ rest} = refl ∷ check {_} {list} {rest}
check {_} {[]} {[]} = []


spec : Test $ (((1 ∷ 2 ∷ 3 ∷ []) ++ []) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
            ∷ (((1 ∷ 2 ∷ []) ++ (3 ∷ [])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
            ∷ (((1 ∷ []) ++ (2 ∷ 3 ∷ [])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
            ∷ []
spec = check
