{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestBishop.Inductive where

open import Data.List public
open import Data.List.Membership public
open import Prelude

ℬ : Type a → Type a
ℬ A = Σ[ xs ⦂ List A ] Π[ x ⦂ A ] x ∈! xs
