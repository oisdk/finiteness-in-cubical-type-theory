{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestBishop.Isomorphism where

open import Prelude
open import Data.Fin
open import Data.Fin.Properties

open import Container.List.Isomorphism

import Cardinality.Finite.ManifestBishop.Inductive as 𝕃
import Cardinality.Finite.ManifestBishop.Container as ℒ

open import Cardinality.Finite.SplitEnumerable.Isomorphism

open import Data.Nat.Properties

∈!ℒ⇒∈!𝕃 : ∀ (x : A) l (xs : Fin l → A) → x ℒ.∈! (l , xs) → x 𝕃.∈! ℒ→𝕃 (l , xs)
∈!ℒ⇒∈!𝕃 x (suc l) xs ((f0   , p) , u) = (f0 , p) , lemma
  where
  lemma : (y : x 𝕃.∈ ℒ→𝕃 (suc l , xs)) → (f0 , p) ≡ y
  lemma (f0   , q) = cong (∈ℒ⇒∈𝕃 x (suc l , xs)) (u (f0 , q))
  lemma (fs m , q) =
    let o , r = subst (x ℒ.∈_) (ℒ→𝕃→ℒ l (xs ∘ fs)) (m , q)
    in ⊥-elim (znots (cong (FinToℕ ∘ fst) (u (fs o , r))))
∈!ℒ⇒∈!𝕃 x (suc l) xs ((fs n , p) , u) = 𝕃.push! xs0≢x (∈!ℒ⇒∈!𝕃 x l (xs ∘ fs) ((n , p) , uxss))
  where
  xs0≢x : xs f0 ≢ x
  xs0≢x xs0≡x = snotz (cong (FinToℕ ∘ fst) (u (f0 , xs0≡x)))

  uxss : (y : x ℒ.∈ (l , xs ∘ fs)) → (n , p) ≡ y
  uxss (m , q) = cong (λ { (f0 , q) → ⊥-elim (xs0≢x q) ; (fs m , q) → m , q}) (u (fs m , q))

𝕃⇔ℒ⟨ℬ⟩ : 𝕃.ℬ A ⇔ ℒ.ℬ A
𝕃⇔ℒ⟨ℬ⟩ .fun (sup , cov) = 𝕃→ℒ sup , cov
𝕃⇔ℒ⟨ℬ⟩ .inv ((l , xs) , cov) = ℒ→𝕃 (l , xs) , λ x → ∈!ℒ⇒∈!𝕃 x l xs (cov x)
𝕃⇔ℒ⟨ℬ⟩ .rightInv (sup , cov) i .fst = 𝕃⇔ℒ .rightInv sup i
𝕃⇔ℒ⟨ℬ⟩ .rightInv ((l , xs) , cov) i .snd x =
  J
    (λ ys ys≡ → (zs : x ℒ.∈! ys) → PathP (λ i → x ℒ.∈! sym ys≡ i) zs (cov x))
    (λ _ → isPropIsContr _ _)
    (sym (ℒ→𝕃→ℒ l xs))
    (∈!ℒ⇒∈!𝕃 x l xs (cov x))
    i
𝕃⇔ℒ⟨ℬ⟩ .leftInv  (sup , cov) i .fst = 𝕃⇔ℒ .leftInv sup i
𝕃⇔ℒ⟨ℬ⟩ .leftInv  (sup , cov) i .snd x =
  J
    (λ ys ys≡ → (zs : x 𝕃.∈! ys) → PathP (λ i → x 𝕃.∈! sym ys≡ i) zs (cov x))
    (λ zs → isPropIsContr _ _)
    (sym (𝕃→ℒ→𝕃 sup))
    (∈!ℒ⇒∈!𝕃 x (𝕃.length sup) (sup 𝕃.!_) (cov x))
    i
