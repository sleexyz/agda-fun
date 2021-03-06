module bin2nat where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

infixl 9 _+_
_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

-- infixl 10 _*_
-- _*_ : Nat → Nat → Nat
-- zero * n = zero
-- suc m * n = n + (m * n)
-- {-# BUILTIN NATTIMES _*_ #-}


data Bin : Set where
  bzero : Bin
  btwice : Bin → Bin
  bstwice : Bin → Bin

bincr : Bin → Bin
bincr bzero = bstwice bzero
bincr (btwice x) = bstwice x
bincr (bstwice x) = btwice (bincr x)

bin2nat : Bin → Nat
bin2nat bzero = zero
bin2nat (btwice x) = bin2nat x + bin2nat x
bin2nat (bstwice x) = 1 + bin2nat x + bin2nat x

nat2bin : Nat → Bin
nat2bin zero = bzero
nat2bin (suc x) = bincr (nat2bin x)


+suc : (x y : Nat) → suc (x + y) ≡ x + suc y
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+0 : ∀ x -> x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

suc-distrib-bin : (x : Nat) → nat2bin (suc x) ≡ bincr (nat2bin x)
suc-distrib-bin zero = refl
suc-distrib-bin (suc x) = refl

bincr-distrib-nat : (x : Bin) → bin2nat (bincr x) ≡ suc (bin2nat x)
bincr-distrib-nat bzero = refl
bincr-distrib-nat (btwice x) = refl
bincr-distrib-nat (bstwice x)
  rewrite bincr-distrib-nat x | +0 (bin2nat x) | sym (+suc (bin2nat x) (bin2nat x)) = refl


conversion-id-nat : (x : Nat) → (bin2nat ∘ nat2bin) x ≡ x
conversion-id-nat zero = refl
conversion-id-nat (suc x)
  rewrite suc-distrib-bin x | bincr-distrib-nat (nat2bin x) | conversion-id-nat x = refl


-- * Now lets try it with ≡-Reasoning

open ≡-Reasoning

conversion-id-nat₁ : (x : Nat) → (bin2nat ∘ nat2bin) x ≡ x
conversion-id-nat₁ zero = refl
conversion-id-nat₁ (suc x) =

    (bin2nat ∘ nat2bin ∘ suc) x

  ≡⟨ cong bin2nat (suc-distrib-bin x) ⟩

    (bin2nat ∘ bincr ∘ nat2bin) x

  ≡⟨ bincr-distrib-nat (nat2bin x) ⟩

    (suc ∘ bin2nat ∘ nat2bin) x

  ≡⟨ cong suc (conversion-id-nat₁ x) ⟩

    suc x

  ∎


-- repeat : ∀{l}{A : Set l} → Nat → (A → A) → A → A
-- repeat zero _ x = x
-- repeat (suc n) f x = f (repeat n f x)

-- _+b_ : Bin → Bin → Bin
-- x +b y = repeat (bin2nat x) bincr y

-- -- | The proof hinges on this...
-- -- Which is simply not true...
-- btwice+b : (x : Bin) → (x +b x ≡ btwice x)
-- btwice+b x = {!!}

-- bincr+b : (x y : Bin) →  bincr x +b y ≡ bincr (x +b y)
-- bincr+b bzero y = refl
-- bincr+b (btwice x) y = refl
-- bincr+b (bstwice x) y
--   rewrite
--     bincr+b x y
--   | +0 (bin2nat x)
--   | +0 (bin2nat (bincr x))
--   | bincr+b (btwice x) y
--   | bincr-distrib-nat x
--   | sym (+suc (bin2nat x) (bin2nat x))
--   | suc-distrib-bin (bin2nat x)
--   = refl

-- nat2bin-addition-linear : (x y : Nat) → nat2bin (x + y) ≡ nat2bin x +b nat2bin y
-- nat2bin-addition-linear zero y = refl
-- nat2bin-addition-linear (suc x) y rewrite
--     nat2bin-addition-linear x y
--   | bincr+b (nat2bin x) (nat2bin y)
--   = refl

-- bin-roundtrip-id : (x : Bin) → (nat2bin (bin2nat x)) ≡ x
-- bin-roundtrip-id bzero = refl
-- bin-roundtrip-id (btwice x) rewrite
--     refl
--   | nat2bin-addition-linear (bin2nat x) (bin2nat x)
--   | bin-roundtrip-id x
--   | btwice+b x
--   = refl
-- bin-roundtrip-id (bstwice x) rewrite
--     refl
--   | nat2bin-addition-linear (bin2nat x) (bin2nat x)
--   | bin-roundtrip-id xencoding tests in type agda
--   | btwice+b x
--   = refl

bnorm : Bin → Bin
bnorm = nat2bin ∘ bin2nat

bnorm-idemp : (x : Bin) → (bnorm ∘ bnorm) x ≡ bnorm x
bnorm-idemp x rewrite conversion-id-nat (bin2nat x) = refl

-- | tfw you realize your functions are β-equivalent :p
conversion-id-normalized-bin : (x : Bin) → (nat2bin ∘ bin2nat ∘ bnorm) x ≡ bnorm x
conversion-id-normalized-bin = bnorm-idemp

bnorm-idemp₂ : (x : Bin) → (bnorm ∘ bnorm) x ≡ bnorm x
bnorm-idemp₂ x = (nat2bin ∘ bin2nat ∘ nat2bin ∘ bin2nat) x
  ≡⟨ cong nat2bin (conversion-id-nat (bin2nat x)) ⟩
  refl
