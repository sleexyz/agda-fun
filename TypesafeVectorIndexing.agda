-- | type safe vector indexing

module TypesafeVectorIndexing where

module SemiManual where

  open import Data.Nat

  data Vec (a : Set) : ℕ → Set where
    [] : Vec a 0
    _∷_ : {n : ℕ} → a → Vec a n → Vec a (suc n)

  suc-monotone : {a b : ℕ} → a < b → suc a < suc b
  suc-monotone p = s≤s p

  suc-monotone-inverse : {a b : ℕ} → suc a < suc b → a < b
  suc-monotone-inverse (s≤s p) = p

  get : {a : Set} {j : ℕ} → (i : ℕ) →  Vec a j → (i < j) → a
  get zero [] ()
  get zero (x ∷ xs) refl = x
  get (suc i) [] ()
  get {_} {suc n} (suc i) (x ∷ xs) p = get i xs (suc-monotone-inverse p)


module Manual where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {n m : ℕ} → (n ≤ m) → suc n ≤ suc m

  _<_ : ℕ → ℕ → Set
  a < b = suc a ≤ b

  data Vec (a : Set) : ℕ → Set where
    [] : Vec a zero
    _∷_ : {n : ℕ} → a → Vec a n → Vec a (suc n)

  suc-monotone : {a b : ℕ} → a < b → suc a < suc b
  suc-monotone p = s≤s p

  suc-monotone-inverse : {a b : ℕ} → suc a < suc b → a < b
  suc-monotone-inverse (s≤s p) = p

  get : {a : Set} {j : ℕ} → (i : ℕ) →  Vec a j → (i < j) → a
  get zero [] ()
  get zero (x ∷ xs) refl = x
  get (suc i) [] ()
  get {_} {suc n} (suc i) (x ∷ xs) p = get i xs (suc-monotone-inverse p)

module Manual2 where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  data Vec (a : Set) : ℕ → Set where
    [] : Vec a zero
    _∷_ : {n : ℕ} → a → Vec a n → Vec a (suc n)

  -- Thanks to Antonis for showing me this trick:
  -- which is derived from Conor McBride's I am not a number - I am free variable paper

  data Index : ℕ → Set where
    top : {n : ℕ} → Index (suc n)
    next : {n : ℕ} → Index n → Index (suc n)

  get : {a : Set} {n : ℕ} → Index n → Vec a n → a
  get top (x ∷ xs) = x
  get (next i) (x ∷ xs) = get i xs
