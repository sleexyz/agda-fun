module VFPIA where

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
_ || true = true
_ || _ = false

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

-- | Propositional Equality
-- The only way for this identity type to type check
-- is if x and y are the same type
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

cong : ∀ {a} {A B : Set a} { x y : A}
     → (f : A → B)
     → x ≡ y
     → f x ≡ f y
cong f refl = refl


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
-- ||-cong₁ refl = refl
||-cong₁ p rewrite p = refl


ite-same : ∀{a}{A : Set a} →
           ∀(b : 𝔹) (x : A) →
           (if b then x else x) ≡ x
ite-same true x = refl
ite-same false x = refl

𝔹-contra : (false ≡ true) → ∀ {P : Set} → P
𝔹-contra ()


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
+0 0 =  refl
+0 (suc x) rewrite +0 x =  refl

-- (suc x) + 0 ≡ suc x
-- suc (x + 0) ≡ suc x
-- [ given a proof x + 0 ≡ x, substitute x + 0 for x ]
-- suc x ≡ suc x

+assoc : (X Y Z : ℕ) → (X + Y) + Z ≡ X + (Y + Z)
+assoc 0 y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : (x y : ℕ) → suc (x + y) ≡ x + suc y
+suc 0 y = refl
+suc (suc x) y rewrite +suc x y = refl

comm+ : (x y : ℕ) -> x + y ≡ y + x
comm+ 0 y rewrite +0 y = refl
comm+ (suc x) y rewrite comm+ x y | +suc y x = refl


_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)


*distrib : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*distrib 0 y z = refl
*distrib (suc x) y z rewrite *distrib x y z | +assoc z (x * z) (y * z) = refl

*id0 : (x : ℕ) → x * 0 ≡ 0
*id0 0 = refl
*id0 (suc n) = *id0 n

*comm : (x y : ℕ) → x * y ≡ y * x
*comm x 0 rewrite *id0 x = refl
*comm x (suc y) rewrite *comm y x | *distrib x 1 y | + comm=  {!!}




-- | implicit arguments via inference
id : {T : Set} → T → T
id = λ x → x

fac : ℕ → ℕ
fac zero = 1
fac (suc n) = suc n * fac n

foo : ℕ
foo = fac 7

data _even : ℕ -> Set where
  ZERO : zero even
  STEP : {x : ℕ} -> x even -> suc (suc x) even

proof1 : 8 even
proof1 = STEP (STEP (STEP (STEP ZERO)))


proof_b : (X : ℕ) -> (X + 0) ≡ X
proof_b zero = refl
proof_b (suc n) = cong suc (proof_b n)


proof+commutative : {X Y : ℕ} → (X + Y) ≡ (Y + X)
proof+commutative = {!!}

proof2 : {Y : ℕ} → Y even -> (0 + Y) even
proof2 a = a

-- proof3 : {X Y : Nat} → X even -> Y even -> (X + Y) even


