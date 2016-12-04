module FoldFusion where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Function
open ≡-Reasoning

data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A

map : ∀{a b} {A : Set a} {B : Set b} →
  (A → B) →
  List A →
  List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀{a b} {A : Set a} {B : Set b} →
  (A → B → B) →
  B →
  List A →
  B
foldr f e [] = e
foldr f e (x ∷ xs) = f x (foldr f e xs)

fold-fusion : ∀{a b c}
  {A : Set a} →
  {B : Set b} →
  {C : Set c} →
  (f : A → B → B) →
  (e : B) →
  (g : A → C → C) →
  (h : B → C) →
  (prop : (x : A) → (y : B) → h (f x y) ≡ g x (h y)) →
  (xs : List A) →
  h (foldr f e xs) ≡ foldr g (h e) xs
fold-fusion f e g h prop [] = refl
fold-fusion f e g h prop (x ∷ xs)
  rewrite
    prop x (foldr f e xs)
  | fold-fusion f e g h prop xs
  = refl

fold-fusion-preorder-reasoning : ∀{a b c}
  {A : Set a} →
  {B : Set b} →
  {C : Set c} →
  (f : A → B → B) →
  (e : B) →
  (g : A → C → C) →
  (h : B → C) →
  (prop : (x : A) → (y : B) → h (f x y) ≡ g x (h y)) →
  (xs : List A) →
  h (foldr f e xs) ≡ foldr g (h e) xs
fold-fusion-preorder-reasoning f e g h prop [] = refl
fold-fusion-preorder-reasoning f e g h prop (x ∷ xs) =
    h (foldr f e (x ∷ xs))
  ≡⟨ refl ⟩
    h (f x (foldr f e xs))
  ≡⟨ prop x (foldr f e xs) ⟩
    g x (h (foldr f e xs))
  ≡⟨ cong (g x) (fold-fusion-preorder-reasoning f e g h prop xs) ⟩
    g x (foldr g (h e) xs)
  ≡⟨ refl ⟩
    foldr g (h e) (x ∷ xs)
  ∎
