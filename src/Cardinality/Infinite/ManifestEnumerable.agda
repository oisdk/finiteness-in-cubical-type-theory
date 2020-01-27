{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Infinite.ManifestEnumerable where

open import Prelude
open import Data.List.Kleene
open import Data.Fin
import Data.Nat as ℕ
open import Data.Nat using (_+_)
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Prelude using (J)
import Data.List.Kleene.Membership as Kleene
open import Codata.Stream
open import Cardinality.Infinite.Split

open import HITs.PropositionalTruncation.Sugar

private
  variable
    u : Level
    U : A → Type u
    s : Level
    S : ℕ → Type s

-- ℰ : Type a → Type a
-- ℰ A = Σ[ xs ⦂ Stream A ] Π[ x ⦂ A ] ∥ x ∈ xs ∥

-- ℰ≡ℕ↠ : ℰ A ≡ (ℕ ↠ A)
-- ℰ≡ℕ↠ = refl

-- _∥Σ∥_ : ℰ A → (∀ x → ℰ (U x)) → ℰ (Σ A U)
-- (xs ∥Σ∥ ys) .fst = cantor (xs .fst) (fst ∘ ys)
-- (xs ∥Σ∥ ys) .snd (x , y) =
--   concat-∈
--     (x , y)
--     (xs .fst * (fst ∘ ys)) ∥$∥
--     ⦇ (*-cover x (xs .fst) y (fst ∘ ys)) (xs .snd x) (ys x .snd y) ⦈
