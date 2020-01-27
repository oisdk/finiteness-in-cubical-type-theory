{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.ManifestEnumerable where

open import Prelude

import Cardinality.Finite.ManifestEnumerable.Inductive as 𝕃
import Cardinality.Finite.ManifestEnumerable.Container as ℒ

open import Cardinality.Finite.ManifestEnumerable.Isomorphism

open import Data.Fin
open import Data.Sigma.Properties
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

module _ where
  open ℒ

  ℰ⇔Fin↠ : ℰ A ⇔ Σ[ n ⦂ ℕ ] (Fin n ↠ A)
  ℰ⇔Fin↠ = reassoc

module _ where
  open 𝕃

  open import Cubical.HITs.S1 hiding (inv)

  ℰ⟨S¹⟩ : ℰ S¹
  ℰ⟨S¹⟩ .fst           = base ∷ []
  ℰ⟨S¹⟩ .snd base      = ∣ f0 , loop ∣
  ℰ⟨S¹⟩ .snd (loop i)  =
    isPropFamS¹ (λ x → ∥ x ∈ base ∷ [] ∥) (λ _ → squash) ∣ f0 , loop ∣ i

  open import HITs.PropositionalTruncation.Properties
  open import Cardinality.Finite.SplitEnumerable.Inductive
  open import Cardinality.Finite.SplitEnumerable
  open import Cardinality.Finite.SplitEnumerable.Isomorphism

  ℰ⇒ℰ! : Discrete A → ℰ A → ℰ! A
  ℰ⇒ℰ! _≟_ E .fst = E .fst
  ℰ⇒ℰ! _≟_ E .snd x = recompute ((_≟ x) ∈? E .fst) (E .snd x)

  ℰ!⇒ℰ : ℰ! A → ℰ A
  ℰ!⇒ℰ E .fst = E .fst
  ℰ!⇒ℰ E .snd x = ∣ E .snd x ∣

  _∥Σ∥_ : {B : A → Type b} → ℰ A → ((x : A) → ℰ (B x)) → ℰ (Σ A B)
  (xs ∥Σ∥ ys) .fst = sup-Σ (xs .fst) (fst ∘ ys)
  (xs ∥Σ∥ ys) .snd (x , y) = ⦇ (cov-Σ x y (xs .fst) (fst ∘ ys)) (xs .snd x) (ys x .snd y) ⦈

  open import Cubical.Foundations.HLevels using (isOfHLevelΣ; hLevelPi)
  open import Cubical.Data.List.Properties using (isOfHLevelList)

  isSet⟨ℰ⟩ : isSet A → isSet (ℰ A)
  isSet⟨ℰ⟩ isSetA =
    isOfHLevelΣ 2
      (isOfHLevelList 0 isSetA)
      λ _ → isProp→isSet (hLevelPi 1 λ _ → squash)

  open import Relation.Nullary.Omniscience
  open import Data.List.Relation.Unary

  private variable p : Level

  ℰ⇒Omniscient : ℰ A → Omniscient p A
  ℰ⇒Omniscient xs P? =
    ∣ Exists.◇? _ P? (xs .fst)
      ∣yes⇒ (λ { (n , p) → (xs .fst ! n , p)})
      ∣no⇒ (λ { ¬P∈xs (x , p) → refute-trunc ¬P∈xs (map₂ (flip (subst _) p ∘ sym) ∥$∥ xs .snd x)  })
