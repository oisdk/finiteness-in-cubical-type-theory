{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestEnumerable.Container where

open import Prelude
open import Data.Fin
open import Container
open import Container.List public
open import Container.Membership (ℕ ▷ Fin) public

ℰ : Type a → Type a
ℰ A = Σ[ xs ⦂ List A ] Π[ x ⦂ A ] ∥ x ∈ xs ∥
