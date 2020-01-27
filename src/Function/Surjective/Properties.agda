{-# OPTIONS --cubical --safe #-}

module Function.Surjective.Properties where

open import Path
open import Function.Fiber
open import Level
open import HITs.PropositionalTruncation
open import Data.Sigma
open import Function.Surjective.Base
open import Function.Injective.Base
open import Function.Injective.Properties
open import Path.Reasoning
open import Relation.Nullary.Discrete

A↠!B⇒B↣A : A ↠! B → B ↣ A
A↠!B⇒B↣A (f , surj) .fst x = surj x .fst
A↠!B⇒B↣A (f , surj) .snd x y f⁻¹⟨x⟩≡f⁻¹⟨y⟩ =
  x                ≡˘⟨ surj x .snd ⟩
  f (surj x .fst)  ≡⟨ cong f f⁻¹⟨x⟩≡f⁻¹⟨y⟩ ⟩
  f (surj y .fst)  ≡⟨ surj y .snd ⟩
  y ∎

Discrete↠!A⇒Discrete⟨A⟩ : A ↠! B → Discrete A → Discrete B
Discrete↠!A⇒Discrete⟨A⟩ A↠!B =
  A↣Discrete⇒Discrete⟨A⟩ (A↠!B⇒B↣A A↠!B)
