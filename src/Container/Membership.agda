{-# OPTIONS --safe --cubical #-}

open import Container

module Container.Membership {s p} (𝒞 : Container s p) where

open import Prelude
open import HLevels

infixr 5 _∈_ _∈!_
_∈_ : A → ⟦ 𝒞 ⟧ A → Type _
x ∈ xs = fiber (xs . snd) x

_∈!_ : A → ⟦ 𝒞 ⟧ A → Type _
x ∈! xs = isContr (x ∈ xs)
