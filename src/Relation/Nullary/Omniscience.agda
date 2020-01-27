{-# OPTIONS --cubical --safe --postfix-projections #-}

module Relation.Nullary.Omniscience where

open import Prelude
open import Relation.Nullary.Decidable
open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Decidable.Logic
open import Relation.Nullary
open import Data.Bool using (bool)

private
  variable
    p : Level
    P : A → Type p

Omniscient Exhaustible : ∀ p {a} → Type a → Type _
Omniscient   p A = ∀ {P : A → Type p} → Decidable P → Dec (∃  P)
Exhaustible  p A = ∀ {P : A → Type p} → Decidable P → Dec (∀′ P)

Omniscient→Exhaustible : ∀ {p} → Omniscient p A → Exhaustible p A
Omniscient→Exhaustible omn P? =
  map-dec
    (λ ¬∃P x → Dec→Stable _ (P? x) (¬∃P ∘ (x ,_)))
    (λ ¬∃P ∀P → ¬∃P λ p → p .snd (∀P (p .fst)))
    (! (omn (! ∘ P?)))
