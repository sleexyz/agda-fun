module bin2nat where

open import Relation.Binary.PropositionalEquality
open import Function

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

infixl 9 _+_
_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

infixl 10 _*_
_*_ : Nat → Nat → Nat
zero * n = zero
suc m * n = n + (m * n)
{-# BUILTIN NATTIMES _*_ #-}


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
bin2nat (btwice x) = 2 * (bin2nat x)
bin2nat (bstwice x) = 1 + 2 * (bin2nat x)

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


nat-roundtrip-id : (x : Nat) → (bin2nat ∘ nat2bin) x ≡ x
nat-roundtrip-id zero = refl
nat-roundtrip-id (suc x)
  rewrite suc-distrib-bin x | bincr-distrib-nat (nat2bin x) | nat-roundtrip-id x = refl


-- * Now lets try it with ≡-Reasoning

open ≡-Reasoning

nat-roundtrip-id2 : (x : Nat) → (bin2nat ∘ nat2bin) x ≡ x
nat-roundtrip-id2 zero = refl
nat-roundtrip-id2 (suc x) =

    (bin2nat ∘ nat2bin ∘ suc) x

  ≡⟨ cong bin2nat (suc-distrib-bin x) ⟩

    (bin2nat ∘ bincr ∘ nat2bin) x

  ≡⟨ bincr-distrib-nat (nat2bin x) ⟩

    (suc ∘ bin2nat ∘ nat2bin) x

  ≡⟨ cong suc (nat-roundtrip-id2 x) ⟩

    suc x

  ∎
