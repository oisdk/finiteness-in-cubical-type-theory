{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestEnumerable.Inductive where

open import Prelude
open import Data.List public
open import Data.List.Membership public

ℰ : Type a → Type a
ℰ A = Σ[ xs ⦂ List A ] Π[ x ⦂ A ] ∥ x ∈ xs ∥
