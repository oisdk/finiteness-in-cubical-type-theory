{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable.Isomorphism where

open import Prelude
open import Container
open import Container.List
open import Data.Fin
open import Container.Membership (ℕ ▷ Fin)
open import Path.Reasoning
open import Data.Sigma.Properties
open import Function.Surjective.Properties
open import Data.Fin.Properties
import Data.List.Membership as 𝕃
open import Container.List.Isomorphism
open import Data.Nat.Properties
open import Data.List using (_∷_; []; List)
import Cardinality.Finite.SplitEnumerable.Container as ℒ
import Cardinality.Finite.SplitEnumerable.Inductive as 𝕃

∈ℒ⇒∈𝕃 : ∀ (x : A) (xs : ⟦ ℕ ▷ Fin ⟧ A) → x ∈ xs → x 𝕃.∈ ℒ→𝕃 xs
∈ℒ⇒∈𝕃 x (suc l , xs) (f0   , p) = f0 , p
∈ℒ⇒∈𝕃 x (suc l , xs) (fs n , p) = 𝕃.push (∈ℒ⇒∈𝕃 x (l , xs ∘ fs) (n , p))

𝕃⇔ℒ⟨ℰ!⟩ : 𝕃.ℰ! A ⇔ ℒ.ℰ! A
𝕃⇔ℒ⟨ℰ!⟩ .fun (sup , cov) = 𝕃→ℒ sup , cov
𝕃⇔ℒ⟨ℰ!⟩ .inv (sup , cov) = ℒ→𝕃 sup , λ x → ∈ℒ⇒∈𝕃 x sup (cov x)
𝕃⇔ℒ⟨ℰ!⟩ .rightInv (sup , cov) i .fst = 𝕃⇔ℒ .rightInv sup i
𝕃⇔ℒ⟨ℰ!⟩ .rightInv (sup , cov) i .snd x = ∈ℒ⇒∈𝕃-rightInv sup (cov x) i
  where
  ∈ℒ⇒∈𝕃-rightInv : ∀ xs x∈xs →
    PathP (λ i → x ∈ 𝕃⇔ℒ .rightInv xs i)
      (∈ℒ⇒∈𝕃 x xs x∈xs) x∈xs
  ∈ℒ⇒∈𝕃-rightInv (suc l , xs) (f0   , x∈xs) i = f0 , x∈xs
  ∈ℒ⇒∈𝕃-rightInv (suc l , xs) (fs n , x∈xs) i =
    let m , q = ∈ℒ⇒∈𝕃-rightInv (l , xs ∘ fs) (n , x∈xs) i
    in fs m , q
𝕃⇔ℒ⟨ℰ!⟩ .leftInv (sup , cov) i .fst = 𝕃⇔ℒ .leftInv sup i
𝕃⇔ℒ⟨ℰ!⟩ .leftInv (sup , cov) i .snd x = ∈ℒ⇒∈𝕃-leftInv sup (cov x) i
  where
  ∈ℒ⇒∈𝕃-leftInv : ∀ xs x∈xs →
    PathP (λ i → x 𝕃.∈ 𝕃→ℒ→𝕃 xs i)
      (∈ℒ⇒∈𝕃 x (𝕃→ℒ xs) x∈xs) x∈xs
  ∈ℒ⇒∈𝕃-leftInv (_ ∷ xs) (f0   , x∈xs) i = f0 , x∈xs
  ∈ℒ⇒∈𝕃-leftInv (_ ∷ xs) (fs n , x∈xs) i =
    let m , p = ∈ℒ⇒∈𝕃-leftInv xs (n , x∈xs) i
    in fs m , p

