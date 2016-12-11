module Category where

open import Level

module UnparameteterizedPreCategory where
  record PreCategory {o l : Level} : Set (suc (o ⊔ l)) where
    field
      k : Set o
      _~>_ : k → k → Set l
      id : {x : k} → x ~> x
      _∘_ : {x y z : k} → y ~> z → x ~> y → x ~> z

  open PreCategory {{...}} public

  instance agda : PreCategory
  agda = record
    { k = Set
    ; _~>_ = λ a b → a → b
    ; id = λ x → x
    ; _∘_ = λ g f → λ x → g (f x)
    }

  example-usage : {x : Set} → x ~> x
  example-usage = id ∘ id

module ParameterizedPreCategory where
  record PreCategory {o l : Level} (k : Set o) (_~>_ : k → k → Set l) : Set (suc (o ⊔ l)) where
    field
      id : {x : k} → x ~> x
      _∘_ : {x y z : k} → y ~> z → x ~> y → x ~> z

  open PreCategory {{...}} public

  instance agda : PreCategory Set (λ a b → a → b)
  agda = record
    { id = λ x → x
    ; _∘_ = λ g f → λ x → g (f x)
    }

  example-usage : {x : Set} → x → x
  example-usage = id ∘ id
