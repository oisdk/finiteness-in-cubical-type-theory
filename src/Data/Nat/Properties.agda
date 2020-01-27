{-# OPTIONS --cubical --safe #-}

module Data.Nat.Properties where

open import Data.Nat.Base
import Agda.Builtin.Nat as Nat
open import Prelude
open import Cubical.Data.Nat using (caseNat; znots; snotz; injSuc) public

pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero

correct-== : ∀ n m → Reflects (n ≡ m) (n Nat.== m)
correct-== zero zero = ofʸ refl
correct-== zero (suc m) = ofⁿ znots
correct-== (suc n) zero = ofⁿ snotz
correct-== (suc n) (suc m) =
  map-reflects (cong suc) (λ contra prf  → contra (cong pred prf)) (correct-== n m)

discreteℕ : Discrete ℕ
discreteℕ n m .does = n Nat.== m
discreteℕ n m .why  = correct-== n m

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-idʳ : ∀ x → x + 0 ≡ x
+-idʳ zero     = refl
+-idʳ (suc x)  = cong suc (+-idʳ x)

+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero = +-idʳ x
+-comm x (suc y) = +-suc x y ; cong suc (+-comm x y)
