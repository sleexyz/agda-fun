module TestsInTypes where

module TestInTypes-0 where
  open import Relation.Binary.PropositionalEquality
  open import Data.Product using (_×_; _,_)
  open import Data.List

  infix 4 _shouldBe_
  _shouldBe_ = _≡_

  -- * Attempt 0 : manual

  test1 :
      (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
    × (((1 ∷ 2 ∷ []) ++ (3 ∷ [])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
    × (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
  test1 =
      refl
    , refl
    , refl

module TestsInTypes-1 where
  open import Relation.Binary.PropositionalEquality
  open import Data.Product using (_×_; _,_)
  open import Data.List
  open import Data.Unit using (⊤)
  open import Data.Empty
  open import Level

  infix 4 _shouldBe_
  _shouldBe_ = _≡_

  -- * Attempt 1 : propositional equality with ad-hoc polymorphism

  record Testable {a} (A : Set a) : Set (suc a) where
    field check : A

  open Testable {{...}} public

  instance testable-≡ : ∀{a} {A : Set a} {x : A} → Testable (x ≡ x)
  testable-≡ = record {check = refl}

  instance testable-× : ∀{a b} {A : Set a} {B : Set b} {{checkA : Testable A}} {{checkB : Testable B}} → Testable (A × B)
  testable-× = record {check = check , check}

  -- * Example:
  test2-a : 1 shouldBe 1
  test2-a = check

  test2-b : (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
          × (((1 ∷ 2 ∷ []) ++ (3 ∷ [])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
          × (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
  test2-b = check

-- * Attempt 2 : decidable equality: maybe better error messages?

module TestsInTypes-2 where
  open import Data.Nat
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  decidable-prop : Dec (zero ≡ zero)
  decidable-prop = zero ≟ zero

  -- might have to look into this


-- * Attempt 3 : heterogenous equality: maybe better error messages?

module TestsInTypes-3 where
  open import Data.Unit
  open import Data.Empty
  open import Data.Nat
  open import Data.Product
  open import Data.List
  open import Relation.Binary.HeterogeneousEquality
  import Level

  infix 4 _shouldBe_
  _shouldBe_ = _≅_

  test1 : ⊤ ≅ ⊤
  test1 = refl

  record Testable {a} (A : Set a) : Set (Level.suc a) where
    field check : A

  open Testable {{...}} public

  instance testable-≡ : ∀{a} {A : Set a} {x : A} → Testable (x ≅ x)
  testable-≡ = record {check = refl}

  instance testable-× : ∀{a b} {A : Set a} {B : Set b} {{checkA : Testable A}} {{checkB : Testable B}} → Testable (A × B)
  testable-× = record {check = check , check}

  test2-a : 1 shouldBe 1
  test2-a = check

  -- hmm, error messages are still bad...

  test2-b : (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
          × (((1 ∷ 2 ∷ []) ++ (3 ∷ [])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
          × (((1 ∷ 2 ∷ 3 ∷ []) ++ ([])) shouldBe (1 ∷ 2 ∷ 3 ∷ []))
  test2-b = check
