{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable.Instances where

open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.ManifestBishop using (_|Π|_)
open import Data.Fin
open import Prelude

instance
  fin-prod : ⦃ lhs : ℰ! A ⦄ ⦃ rhs : ℰ! B ⦄ → ℰ! (A × B)
  fin-prod ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |×| rhs

instance
  fin-sum : ⦃ lhs : ℰ! A ⦄ ⦃ rhs : ℰ! B ⦄ → ℰ! (A ⊎ B)
  fin-sum ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |⊎| rhs

instance
  fin-fun : {A B : Type₀} ⦃ lhs : ℰ! A ⦄ ⦃ rhs : ℰ! B ⦄ → ℰ! (A → B)
  fin-fun ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |Π| λ _ → rhs

instance
  fin-bool : ℰ! Bool
  fin-bool = ℰ!⟨2⟩

instance
  fin-top : ℰ! ⊤
  fin-top = ℰ!⟨⊤⟩

instance
  fin-bot : ℰ! ⊥
  fin-bot = ℰ!⟨⊥⟩
