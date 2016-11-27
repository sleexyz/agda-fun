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
    (1 ∷ 2 ∷ 3 ∷ [] ++ [] shouldBe 1 ∷ 2 ∷ 3 ∷ [])
  × (1 ∷ 2 ∷ [] ++ 3 ∷ [] shouldBe 1 ∷ 2 ∷ 3 ∷ [])
  × (1 ∷ 2 ∷ 3 ∷ [] ++ [] shouldBe 1 ∷ 2 ∷ 3 ∷ [])
test₁ =
    refl
  , refl
  , refl


data Hlist {n} : (xs : List (Set n)) → Set (n) where
  [] : Hlist []
  _∷_ : {x : Set n} {xs : List (Set n)} → x → Hlist xs → Hlist (x ∷ xs)


check : {xs : List Set} → Hlist (map (λ x → x ≡ x) xs)
check {a ∷ rest} = refl ∷ check {rest}
check {[]} = []


-- spec : Hlist ( (1 ∷ 2 ∷ 3 ∷ [] ++ [] shouldBe 1 ∷ 2 ∷ 3 ∷ [])
--              ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ [] shouldBe 1 ∷ 2 ∷ 3 ∷ [])
--              ∷ (1 ∷ [] ++ 2 ∷ 3 ∷ [] shouldBe 1 ∷ 2 ∷ 3 ∷ [])
--              ∷ []
--              )
-- spec = {!!}
