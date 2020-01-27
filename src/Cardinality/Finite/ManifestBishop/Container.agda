{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestBishop.Container where

open import Prelude
open import Data.Fin
open import Container
open import Container.List public
open import Container.Membership (ℕ ▷ Fin) public

ℬ : Type a → Type a
ℬ A = Σ[ xs ⦂ List A ] Π[ x ⦂ A ] x ∈! xs
