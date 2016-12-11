module GeneralizedIndexedVectors where

open import Level
open import Data.Unit
open import Relation.Binary.PropositionalEquality

-- record PreCategory {lₒ lₘ : Level} (obj : Set lₒ) (_⇒_ : obj → obj → Set lₘ) : Set (suc (lₒ ⊔ lₘ)) where
--   field
--     id : {x : obj} → x ⇒ x
--     _∘_ : {x y z : obj} → y ⇒ z → x ⇒ y → x ⇒ z

-- open PreCategory {{...}} public

module Take1 where
  record Scheme : Set₁ where
    field
      state : Set
      init : state
      a : Set
      getNext : a → state → state

  module Vec (scheme : Scheme) where

    open Scheme {{...}} public

    instance myScheme : Scheme
    myScheme = scheme

    data Vec : state → Set₁ where
      [] : Vec init
      _∷_ : {s : state} → (x : a) → Vec s → Vec (getNext x s)


-- | TODO: get some sleep, and then use decidable relations
-- http://mazzo.li/posts/AgdaSort.html

module Take2 where
  record Scheme : Set₁ where
    field
      state : Set
      init : state
      _⇒_ : state → state → Set
      a : Set
      getNext : a → state → state

  module Vec (scheme : Scheme) where

    open Scheme {{...}} public

    instance myScheme : Scheme
    myScheme = scheme

    data Vec : state → Set₁ where
      [] : Vec init
      _∷_ : {s : state} → (x : a) → Vec s → Vec (getNext x s)
