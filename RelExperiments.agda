module RelExperiments where

-- | https://www.csie.ntu.edu.tw/~b94087/aopa-intro.pdf

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product
open import Level

-- | Decidable binary relations:
Rel : Set → Set → Set1
Rel a b = a → b → Set

_∘_ : {A B C : Set} → (Rel B C) → (Rel A B) → (Rel A C)
(_R_ ∘ _S_) a c = ∃ (λ b → b R c × a S b)

-- | lift a function into relation of propositional equality
fun : {A B : Set} → (A → B) → (Rel A B)
fun f = λ x y → f x ≡ y
