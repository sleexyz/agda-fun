module GeneralizedIndexedVectors where

open import Level
open import Data.Unit

record PreCategory {lₒ lₘ : Level} (obj : Set lₒ) (_⇒_ : obj → obj → Set lₘ) : Set (suc (lₒ ⊔ lₘ)) where
  field
    id : {x : obj} → x ⇒ x
    _∘_ : {x y z : obj} → y ⇒ z → x ⇒ y → x ⇒ z

open PreCategory {{...}} public

record Scheme : Set₁ where
  field
    state : Set
    _⇒_ : state → state → Set
    cat : PreCategory state _⇒_
    a : Set
    f : {x y : state} → a → x ⇒ y

data Vec (scheme : Scheme) : Set → Set₁ where
  [] : Vec scheme ⊤
