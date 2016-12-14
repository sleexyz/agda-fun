module GeneralizedIndexedVectors where

open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core

-- | Generalized indexed vectors, without constraints
module Take1 where
  open import Level

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


-- | GeneralizedIndexedVectors, with constraints!
module Take2 where
  open import Level

  record Scheme : Set₁ where
    field
      state : Set
      init : state
      a : Set
      _~_ : REL a state zero -- rel : a → state → Set
      transition : (x : a) → (s : state) → x ~ s → state

  module Vec (scheme : Scheme) where

    open Scheme {{...}} public

    instance myScheme : Scheme
    myScheme = scheme

    infixr 5 _∷_

    data Vec : state → Set₁ where
      [] : Vec init
      _∷_ : {s : state} → (x : a) → Vec s → {p : x ~ s} → Vec (transition x s p)


module Take2Example where
  open Take2
  open import Data.Nat

  natIVecScheme : Set → Scheme
  natIVecScheme obj = record
    { state = ℕ
    ; init = 0
    ; a = obj
    ; _~_ = λ _ _ → ⊤
    ; transition = λ _ s _ → suc s
    }

  open Vec (natIVecScheme ⊤)

  example-0 : Vec 0
  example-0 = []

  example-1 : Vec 1
  example-1 = tt ∷ []

  example-2 : Vec 2
  example-2 = tt ∷ tt ∷ []

module HomogeneousStructuralRecords1 where
  open Take2
  open import Data.String
  open import Data.List
  open import Data.List.Any
  open Membership-≡

  record Row (x : Set) (y : Set) : Set where
    constructor _-_
    field
      key : x
      value : y

  homogeneousStructuralRecordScheme : Set → Scheme
  homogeneousStructuralRecordScheme obj = record
    { state = List String
    ; init = []
    ; a = Row String obj
    ; _~_ = λ r keys → Row.key r ∈ keys
    ; transition = λ r keys _ → Row.key r ∷ keys
    }

  open Vec (homogeneousStructuralRecordScheme String)

  example-0 : Vec []
  example-0 = []

  -- uh oh, can't automatically derive a proof
  -- example-1 : Vec ("name" ∷ [])
  -- example-1 = ("name" - "asdf") ∷ []

-- | GeneralizedIndexedVectors
module Take3 where
  open import Level
  open import Data.Bool

  record Scheme : Set₁ where
    field
      state : Set
      init : state
      a : Set
      _~_ : a → state → Bool
      transition : (x : a) → (s : state) → (x ~ s ≡ true) → state

  module Vec (scheme : Scheme) where
    open Scheme {{...}} public

    instance myScheme : Scheme
    myScheme = scheme

    infixr 5 _∷_

    data Vec : state → Set₁ where
      [] : Vec init
      _∷_ : {s : state} → (x : a) → Vec s → {p : (x ~ s ≡ true)} → Vec (transition x s p)

  open import Data.String hiding (_==_)
  open import Data.List
  open import Relation.Nullary

  record Row (x : Set) (y : Set) : Set where
    constructor _-_
    field
      key : x
      value : y


  record Eq (a : Set) : Set where
    field
      _==_ : Decidable {A = a} _≡_

  open Eq {{...}}

  _∈_ : {a : Set} → {{eqA : Eq a}} → a → List a → Bool
  x ∈ [] = false
  x ∈ (x₁ ∷ xs) with x == x₁
  x ∈ (x₁ ∷ xs) | yes p = true
  x ∈ (x₁ ∷ xs) | no ¬p = x ∈ xs

  instance eq-String : Eq String
  eq-String = record {_==_ = Data.String._≟_}


  homogeneousStructuralRecordScheme : Set → Scheme
  homogeneousStructuralRecordScheme obj = record
    { state = List String
    ; init = []
    ; a = Row String obj
    ; _~_ = λ r keys → Row.key r ∈ keys
    ; transition = λ r keys _ → Row.key r ∷ keys
    }

  open Vec (homogeneousStructuralRecordScheme String)

  example-0 : Vec []
  example-0 = []

  -- uh oh, can't automatically derive a proof
  example-1 : Vec ("name" ∷ [])
  example-1 = ("name" - "asdf") ∷ []

  -- Haskell gets away with this with automatic proof search
