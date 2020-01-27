{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation.Properties where

open import HITs.PropositionalTruncation
open import Prelude

refute-trunc : ¬ A → ¬ ∥ A ∥
refute-trunc = recPropTrunc isProp⊥

recompute : Dec A → ∥ A ∥ → A
recompute (yes p) _ = p
recompute (no ¬p) p = ⊥-elim (recPropTrunc isProp⊥ ¬p p)
