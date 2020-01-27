{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.Structure where

open import Prelude
open import Data.Fin
open import Data.Nat
open import Data.Nat.Properties

private
  variable
    n m : ℕ

liftˡ : ∀ n m → Fin m → Fin (n + m)
liftˡ zero    m x = x
liftˡ (suc n) m x = fs (liftˡ n m x)

liftʳ : ∀ n m → Fin n → Fin (n + m)
liftʳ (suc n) m f0     = f0
liftʳ (suc n) m (fs x) = fs (liftʳ n m x)




mapl : (A → B) → A ⊎ C → B ⊎ C
mapl f (inl x) = inl (f x)
mapl f (inr x) = inr x

fin-sum-to : ∀ n m → Fin n ⊎ Fin m → Fin (n + m)
fin-sum-to n m = either (liftʳ n m) (liftˡ n m)

fin-sum-from : ∀ n m → Fin (n + m) →  Fin n ⊎ Fin m
fin-sum-from zero    m x      = inr x
fin-sum-from (suc n) m f0     = inl f0
fin-sum-from (suc n) m (fs x) = mapl fs (fin-sum-from n m x)


mapl-distrib : ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d} (xs : A ⊎ B) (h : A → C) (f : C → D) (g : B → D) → either′ f g (mapl h xs) ≡ either′ (f ∘′ h) g xs
mapl-distrib (inl x) h f g = refl
mapl-distrib (inr x) h f g = refl

either-distrib : ∀ {d} {D : Type d} (f : A → C) (g : B → C) (h : C → D) (xs : A ⊎ B) → either′ (h ∘ f) (h ∘ g) xs ≡ h (either′ f g xs)
either-distrib f g h (inl x) = refl
either-distrib f g h (inr x) = refl


open import Path.Reasoning

fin-sum-to-from : ∀ n m x → fin-sum-to n m (fin-sum-from n m x) ≡ x
fin-sum-to-from zero    m x      = refl
fin-sum-to-from (suc n) m f0     = refl
fin-sum-to-from (suc n) m (fs x) =
  fin-sum-to (suc n) m (mapl fs (fin-sum-from n m x)) ≡⟨ mapl-distrib (fin-sum-from n m x) fs (liftʳ (suc n) m) (liftˡ (suc n) m) ⟩
  either (liftʳ (suc n) m ∘ fs) (liftˡ (suc n) m) (fin-sum-from n m x) ≡⟨⟩
  either (fs ∘ liftʳ n m) (fs ∘ liftˡ n m) (fin-sum-from n m x) ≡⟨ either-distrib (liftʳ n m) (liftˡ n m) fs (fin-sum-from n m x) ⟩
  fs (either (liftʳ n m) (liftˡ n m) (fin-sum-from n m x)) ≡⟨ cong fs (fin-sum-to-from n m x) ⟩
  fs x ∎

-- fin-sum-from-to : ∀ n m x → fin-sum-from n m (fin-sum-to n m x) ≡ x
-- fin-sum-from-to n m (inl x) = {!!}
-- fin-sum-from-to n m (inr x) = {!!}

-- fin-sum : ∀ n m → Fin n ⊎ Fin m ⇔ Fin (n + m)
-- fin-sum n m .fun = fin-sum-to n m
-- fin-sum n m .inv = fin-sum-from n m
-- fin-sum n m .rightInv = fin-sum-to-from n m
-- fin-sum n m .leftInv = fin-sum-from-to n m
