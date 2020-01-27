{-# OPTIONS --safe --cubical #-}

module Container where

open import Prelude

infix 5 _▷_
record Container (s p : Level) : Type (ℓsuc (s ℓ⊔ p)) where
  constructor _▷_
  field
    Shape    : Type s
    Position : Shape → Type p
open Container public

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ℓ⊔ p ℓ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ[ s ⦂ S ] (P s → X)
