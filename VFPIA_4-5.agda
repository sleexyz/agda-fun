module VFPIA_4-5 where

open import VFPIA_1-3

data List {l} (A : Set l) : Set l where
  [] : List A
  _::_ : A → List A → List A

infixr 5 _::_

length : ∀{l} {A : Set l} → List A -> ℕ
length [] = 0
length (x :: xs) = suc (length xs)

length-example : length (1 :: 1 :: []) ≡ 2
length-example = refl

_++_ : ∀{l} {A : Set l} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀{l m} {A : Set l} {B : Set m} →
  (A → B) →
  List A →
  List B
map _ [] = []
map f (x :: xs) = f x :: map f xs

filter : ∀{l} {A : Set l} →
  (A → 𝔹) →
  List A →
  List A
filter _ [] = []
filter pred (x :: xs) =
  if pred x then x :: r else r
  where
    r = filter pred xs

filter-test : filter isEven (1 :: 2 :: 3 :: 4 :: []) ≡ (2 :: 4 :: [])
filter-test = refl

remove : ∀{l} {A : Set l} →
  (eq : A → A → 𝔹) →
  (a : A) →
  (xs : List A) →
  List A
remove eq a = filter (eq a)

data maybe {l} (A : Set l) : Set l where
  just : A → maybe A
  nothing : maybe A


nth : ∀{l} {A : Set l} → (xs : List A) → (n : ℕ) → maybe A
nth [] _ = nothing
nth (x :: xs) zero = just x
nth (x :: xs) (suc n) = nth xs n

-- slow!
sreverse : {A : Set} → List A → List A
sreverse [] = []
sreverse (x :: xs) = sreverse xs ++ (x :: [])

reverseAux : {A : Set} → List A → List A → List A
reverseAux [] ys = ys
reverseAux (x :: xs) ys = reverseAux xs (x :: ys)

reverse : {A : Set} → List A → List A
reverse xs = reverseAux xs []

length-linear : {A : Set} → (xs ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
length-linear [] ys = refl
length-linear (x :: xs) ys rewrite length-linear xs ys = refl

++-assoc :
  {A : Set}
  (xs : List A)
  (ys : List A)
  (zs : List A) →
  (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs rewrite ++-assoc xs ys zs = refl

length-filter :
  {A : Set}
  (pred : A → 𝔹)
  (xs : List A) →
  length (filter pred xs) ≤ length xs ≡ true
length-filter pred [] = ≤-refl 0
length-filter pred (x :: xs) with pred x
length-filter pred (x :: xs) | true = length-filter pred xs
length-filter pred (x :: xs) | false = ≤-trans {length (filter pred xs)} (length-filter pred xs) (≤-suc (length xs))

-- | To construct an Inspect, we need a proof of another term and an equality
-- Essentially this gives us a way to pattern match on a term and an equality at the same time
-- Dependent sum! Equality type depends on proof of first term!
data Inspect {l} {A : Set l} (x : A) : Set l where
  _,_ : (y : A) (eq : x ≡ y) → Inspect x

-- | construct an inspect
inspect : ∀{l} {A : Set l} (x : A) → Inspect x
inspect x = x , refl

filter-idem :
  ∀{l} {A : Set l}
  (pred : A → 𝔹)
  (xs : List A) →
  (filter pred (filter pred xs)) ≡ filter pred xs
filter-idem pred [] = refl
filter-idem pred (x :: xs) with inspect (pred x)
filter-idem pred (x :: xs) | true , eq
  rewrite eq | eq | filter-idem pred xs = refl
filter-idem pred (x :: xs) | false , eq
  rewrite eq = filter-idem pred xs

length-reverseAux :
  {A : Set}
  (xs : List A)
  (ys : List A) →
  length (reverseAux xs ys) ≡ length ys + length xs
length-reverseAux [] ys
  rewrite +0 (length ys)
  = refl
length-reverseAux (x :: xs) ys
  rewrite length-reverseAux xs ys
  | sym (+suc (length ys) (length xs))
  = {!!}

length-reverse :
  {A : Set}
  (xs : List A) →
  length (reverse xs) ≡ length xs
length-reverse xs = length-reverseAux xs []
