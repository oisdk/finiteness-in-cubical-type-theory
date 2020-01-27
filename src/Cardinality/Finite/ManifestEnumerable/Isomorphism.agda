{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestEnumerable.Isomorphism where

open import Prelude

import Cardinality.Finite.ManifestEnumerable.Container as ℒ
import Cardinality.Finite.ManifestEnumerable.Inductive as 𝕃

open import Container.List.Isomorphism
open import Data.Fin
open import HITs.PropositionalTruncation.Sugar
open import Data.List using (_∷_; [])
open import HITs.PropositionalTruncation
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Data.Sigma.Properties

𝕃⇔ℒ⟨ℰ⟩ : 𝕃.ℰ A ⇔ ℒ.ℰ A
𝕃⇔ℒ⟨ℰ⟩ .fun (sup , cov) = 𝕃→ℒ sup , cov
𝕃⇔ℒ⟨ℰ⟩ .inv (sup , cov) = ℒ→𝕃 sup , λ x → ∈ℒ⇒∈𝕃 x sup ∥$∥ cov x
𝕃⇔ℒ⟨ℰ⟩ .rightInv (sup , cov) = ΣProp≡ (λ xs x y i t → squash (x t) (y t) i) (𝕃⇔ℒ .rightInv sup)
𝕃⇔ℒ⟨ℰ⟩ .leftInv  (sup , cov) = ΣProp≡ (λ xs x y i t → squash (x t) (y t) i) (𝕃⇔ℒ .leftInv sup)
