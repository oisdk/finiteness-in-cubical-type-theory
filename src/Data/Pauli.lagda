\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Pauli where

open import Prelude hiding (I)
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Search
open import Cardinality.Finite.SplitEnumerable.Instances
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Cardinality.Finite.ManifestBishop
open import Data.Fin
open import Relation.Nullary.Decidable.Logic

it : ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x

module Bools where
 infix 4 _≟_
 _≟_ : Discrete (Bool → Bool)
 _≟_ = ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun it)
\end{code}
%<*not-spec>
\begin{code}
 not-spec : Σ[ f ⦂ (Bool → Bool) ] (f ∘ f ≡ id) × (f ≢ id)
 not-spec = ∃↯ⁿ 1 λ f → (f ∘ f ≟ id) && ! (f ≟ id)
\end{code}
%</not-spec>
\begin{code}
open Bools using (not-spec) public
\end{code}
%<*def>
\begin{code}
data Pauli : Type₀ where X Y Z I : Pauli
\end{code}
%</def>
\begin{code}
instance
  ℰ!⟨Pauli⟩ : ℰ! Pauli
  ℰ!⟨Pauli⟩ .fst  = X ∷ Y ∷ Z ∷ I ∷ []
  ℰ!⟨Pauli⟩ .snd X  = f0 , refl
  ℰ!⟨Pauli⟩ .snd Y  = fs f0 , refl
  ℰ!⟨Pauli⟩ .snd Z  = fs (fs f0) , refl
  ℰ!⟨Pauli⟩ .snd I  = fs (fs (fs f0)) , refl

infix 4 _≟_
_≟_ : (x y : Pauli) → Dec (x ≡ y)
_≟_ = ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun ℰ!⟨Pauli⟩)

infixl 6 _·_
_·_ : Pauli → Pauli → Pauli
I  · x  = x
X  · X  = I
X  · Y  = Z
X  · Z  = Y
X  · I  = X
Y  · X  = Z
Y  · Y  = I
Y  · Z  = X
Y  · I  = Y
Z  · X  = Y
Z  · Y  = X
Z  · Z  = I
Z  · I  = Z

cancel-· : ∀ x → x · x ≡ I
cancel-· = ∀↯ⁿ 1 λ x → x · x ≟ I

comm-· : ∀ x y → x · y ≡ y · x
comm-· = ∀↯ⁿ 2 λ x y → x · y ≟ y · x
\end{code}
%<*assoc-prf>
\begin{code}
assoc-· : ∀ x y z → (x · y) · z ≡ x · (y · z)
assoc-· = ∀↯ⁿ 3 λ x y z → (x · y) · z ≟ x · (y · z)
\end{code}
%</assoc-prf>
\begin{code}

\end{code}
