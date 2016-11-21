-- | Booleans and Natural numbers
module VFPIA_1-3 where

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

{-# BUILTIN BOOL 𝔹 #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

not : 𝔹 -> 𝔹
not true = false
not false = true

-_ = not

equiv : 𝔹 -> 𝔹 -> 𝔹
equiv true true = true
equiv true false = false
equiv false true = false
equiv false false = true

infix 7 -_

infixl 5  _||_
_||_ : 𝔹 → 𝔹 → 𝔹
false || false = false
_ || _ = true

infixl 6 _&&_
_&&_ : 𝔹 → 𝔹 → 𝔹
true && true = true
_ && _ = false

if_then_else_ : ∀ {n} {A : Set n} 𝔹 → A → A → A
if true then t else f =  t
if false then t else f =  f

_imp_ : 𝔹 → 𝔹 → 𝔹
true imp true = true
true imp false = false
false imp true = true
false imp false = true

Bool = 𝔹

infixl -60 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

cong : ∀ {a} {A B : Set a} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {a} {A B : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

notnotTrue : - - true ≡ true
notnotTrue = refl

notnotFalse : - - false ≡ false
notnotFalse = refl

-- Dependent product type
notnot-elim : ∀ (b : 𝔹) → - - b ≡ b
notnot-elim true = refl
notnot-elim false = refl

notnot-elim2 : ∀ (b : 𝔹) → - - b ≡ b
notnot-elim2 true = notnotTrue
notnot-elim2 false = notnotFalse

𝔹-contra : (false ≡ true) → ∀ {P : Set} → P
𝔹-contra ()

&&-same : ∀ {b} → b && b ≡ b
&&-same{true} = refl
&&-same{false} = refl

||-same : ∀ {b} → b || b ≡ b
||-same{true} = refl
||-same{false} = refl

||≡false₁ : ∀ {b1 b2} -> b1 || b2 ≡ false → b1 ≡ false
||≡false₁ {false} p = refl
||≡false₁ {true} ()

||-cong₁ : ∀ {b1 b1' b2} → b1 ≡ b1' -> (b1 || b2) ≡ (b1' || b2)
||-cong₁ refl = refl

cond-same : ∀{a}{A : Set a} → ∀(b : 𝔹) (x : A) → (if b then x else x) ≡ x
cond-same true x = refl
cond-same false x = refl



-- * Naturals

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

Nat = ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 10 _*_
infixl 9 _+_

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

pred : ℕ -> ℕ
pred zero = zero
pred (suc n) = n

0+ : (x : ℕ) -> 0 + x ≡ x
0+ x = refl

0+' : ∀ x -> 0 + x ≡ x
0+' x = refl

+0 : ∀ x -> x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : (X Y Z : ℕ) → (X + Y) + Z ≡ X + (Y + Z)
+assoc 0 y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : (x y : ℕ) → suc (x + y) ≡ x + suc y
+suc 0 y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm : (x y : ℕ) -> x + y ≡ y + x
+comm 0 y rewrite +0 y = refl
+comm (suc x) y  rewrite +comm x y | +suc y x = refl

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

0* : (x : ℕ) -> (0 * x) ≡ 0
0* _ = refl

*0 : (x : ℕ) -> (x * 0) ≡ 0
*0 0 = refl
*0 (suc n) rewrite *0 n = refl

*rdistrib : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*rdistrib 0 y z = refl
*rdistrib (suc x) y z rewrite *rdistrib x y z | +assoc z (x * z) (y * z) = refl

*id0 : (x : ℕ) → x * 0 ≡ 0
*id0 0 = refl
*id0 (suc n) = *id0 n

*suc : (x y : ℕ) -> x * suc y ≡ x + x * y
*suc 0 y = refl
*suc (suc n) y rewrite *suc n y | +comm n (y + (n * y)) | +assoc y (n * y) n | +comm n (n * y)  = refl

*comm : (x y : ℕ) → x * y ≡ y * x
*comm 0 y rewrite *id0 y = refl
*comm (suc x) y rewrite *comm x y | *suc y x = refl

*ldistrib : (x y z : ℕ) -> z * (x + y) ≡ z * x + z * y
*ldistrib x y z rewrite *comm z (x + y) | *rdistrib x y z | *comm x z | *comm y z  = refl

*assoc : (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
*assoc zero y z = refl
*assoc (suc x) y z rewrite *assoc x y z | *rdistrib y (x * y) z = refl

_<_ : ℕ → ℕ → 𝔹
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

<0 : ∀ (x : ℕ) -> x < 0 ≡ false
<0 (zero) = refl
<0 (suc x) = refl

<trans : ∀ {x y z : ℕ} -> x < y ≡ true -> y < z ≡ true -> x < z ≡ true
<trans {x} {0} p1 p2 rewrite <0 x = 𝔹-contra p1
<trans {zero} {suc y} {zero} p1 ()
<trans {zero} {suc y} {suc z} p1 p2 = refl
<trans {suc x} {suc y} {zero} p1 ()
<trans {suc x} {suc y} {suc z} p1 p2 = <trans {x} {y} {z} p1 p2


_==_ : ℕ → ℕ → 𝔹
zero == zero = true
zero == suc y₁ = false
suc x₁ == zero = false
suc x₁ == suc y₁ = x₁ == y₁

_≤_ : ℕ → ℕ → 𝔹
-- zero ≤ _ = true
-- suc x ≤ zero = false
-- suc x ≤ suc y = x ≤ y
x ≤ y = x < y || x == y

==refl : ∀ (x : ℕ) → x == x ≡ true
==refl zero = refl
==refl (suc x) = ==refl x

==to≡ : ∀ {x y : ℕ} → (x == y) ≡ true → x ≡ y
==to≡ {zero} {zero} refl = refl
==to≡ {zero} {suc y} ()
==to≡ {suc x} {zero} ()
==to≡ {suc x} {suc y} p rewrite ==to≡ {x} {y} p = refl

==from≡ : ∀ {x y : ℕ} → x ≡ y → (x == y) ≡ true
==from≡ {x} refl = ==refl x

isEven : ℕ -> 𝔹
isOdd : ℕ -> 𝔹
isEven zero = true
isEven (suc x) = - isOdd x
isOdd zero = true
isOdd (suc x) = - isEven x

≤-refl : ∀(x : ℕ) → x ≤ x ≡ true
≤-refl zero = refl
≤-refl (suc x) = ≤-refl x

≤-trans :
  ∀ {x y z : ℕ}
  (p1 : x ≤ y ≡ true )
  (p2 : y ≤ z ≡ true ) →
  x ≤ z ≡ true
≤-trans {suc _} {zero} {_} ()
≤-trans {suc _} {suc _} {zero} p1 ()
≤-trans {zero} {zero} p1 p2 = p2
≤-trans {zero} {suc y} {zero} p1 p2 = refl
≤-trans {zero} {suc y} {suc z} p1 p2 = refl
≤-trans {suc x} {suc y} {suc z} p1 p2 = ≤-trans {x} {y} {z} p1 p2

≤-suc :
  ∀ (x : ℕ) →
  x ≤ suc x ≡ true
≤-suc zero = refl
≤-suc (suc x) = ≤-suc x
