{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.SplitEnumerable where

open import Prelude
open import Container
open import Data.Fin
open import Data.Sigma.Properties
open import Function.Surjective.Properties
open import Data.Fin.Properties

import Cardinality.Finite.SplitEnumerable.Container as ℒ
import Cardinality.Finite.SplitEnumerable.Inductive as 𝕃
open import Cardinality.Finite.SplitEnumerable.Isomorphism

open import Data.Nat.Literals
open import Data.Fin.Literals
open import Literals.Number

private
  variable
    u : Level
    U : A → Type u

module _ {a} {A : Type a} where
 open ℒ
 open import Container.List
 open import Container.Membership (ℕ ▷ Fin)
 open import Relation.Binary.Equivalence.Reasoning (⇔-equiv {a})

 ℰ!⇔Fin↠! : ℰ! A ⇔ Σ[ n ⦂ ℕ ] (Fin n ↠! A)
 ℰ!⇔Fin↠! =
   ℰ! A                                                  ≋⟨⟩ -- ℰ!
   Σ[ xs ⦂ List A ] Π[ x ⦂ A ] x ∈ xs                    ≋⟨⟩ -- ∈
   Σ[ xs ⦂ List A ] Π[ x ⦂ A ] fiber (xs .snd) x         ≋⟨ reassoc ⟩
   Σ[ n ⦂ ℕ ] Σ[ f ⦂ (Fin n → A) ] Π[ x ⦂ A ] fiber f x  ≋⟨⟩ -- ↠!
   Σ[ n ⦂ ℕ ] (Fin n ↠! A) ∎

 ℰ!⇒Discrete : ℰ! A → Discrete A
 ℰ!⇒Discrete = flip Discrete↠!A⇒Discrete⟨A⟩ discreteFin
             ∘ snd
             ∘ ℰ!⇔Fin↠! .fun

module _ where
 open 𝕃
 open import Data.List.Sugar hiding ([_])
 open import Data.List.Syntax
 open import Data.List.Membership

 ℰ!⟨2⟩ : ℰ! Bool
 ℰ!⟨2⟩ .fst = [ false , true ]
 ℰ!⟨2⟩ .snd false  = 0  , refl
 ℰ!⟨2⟩ .snd true   = 1  , refl

 ℰ!⟨⊤⟩ : ℰ! ⊤
 ℰ!⟨⊤⟩ .fst = [ tt ]
 ℰ!⟨⊤⟩ .snd _ = 0 , refl

 ℰ!⟨⊥⟩ : ℰ! ⊥
 ℰ!⟨⊥⟩ = [] , λ ()

 sup-Σ : List A → (∀ x → List (U x)) → List (Σ A U)
 sup-Σ xs ys = do  x ← xs
                   y ← ys x
                   [ x , y ]

 cov-Σ : (x : A)
       → (y : U x)
       → (xs : List A)
       → (ys : ∀ x → List (U x))
       → x ∈ xs
       → y ∈ ys x
       → (x , y) ∈ sup-Σ xs ys
 cov-Σ xᵢ yᵢ (x ∷ xs) ys (fs n , x∈xs) y∈ys =
   map (x ,_) (ys x) ++◇ cov-Σ xᵢ yᵢ xs ys (n , x∈xs) y∈ys
 cov-Σ xᵢ yᵢ (x ∷ xs) ys (f0  , x∈xs) y∈ys =
   subst (λ x′ → (xᵢ , yᵢ) ∈ sup-Σ (x′ ∷ xs) ys) (sym x∈xs)
   (map (xᵢ ,_) (ys xᵢ) ◇++ cong-∈ (xᵢ ,_) (ys xᵢ) y∈ys)

 _|Σ|_ : ℰ! A → (∀ x → ℰ! (U x)) → ℰ! (Σ A U)
 (xs |Σ| ys) .fst = sup-Σ (xs .fst) (fst ∘ ys)
 (xs |Σ| ys) .snd (x , y) = cov-Σ x y (xs .fst) (fst ∘ ys) (xs .snd x) (ys x .snd y)

 _|×|_ : ℰ! A → ℰ! B → ℰ! (A × B)
 xs |×| ys = xs |Σ| const ys

 _|⊎|_ : ℰ! A → ℰ! B → ℰ! (A ⊎ B)
 (xs |⊎| ys) .fst = map inl (xs .fst) ++ map inr (ys .fst)
 (xs |⊎| ys) .snd (inl x) = map inl (xs .fst) ◇++ cong-∈ inl (xs .fst) (xs .snd x)
 (xs |⊎| ys) .snd (inr y) = map inl (xs .fst) ++◇ cong-∈ inr (ys .fst) (ys .snd y)

 _|+|_ : ℰ! A → ℰ! B → ℰ! (Σ[ t ⦂ Bool ] (if t then A else B))
 xs |+| ys = ℰ!⟨2⟩ |Σ| bool ys xs

 open import Data.Tuple

 ℰ!⟨Tuple⟩ : ∀ {n u} {U : Lift a (Fin n) → Type u} → (∀ i → ℰ! (U i)) → ℰ! (Tuple n U)
 ℰ!⟨Tuple⟩ {n = zero}  f = (_ ∷ []) , λ _ → f0 , refl
 ℰ!⟨Tuple⟩ {n = suc n} f = f (lift f0) |×| ℰ!⟨Tuple⟩ (f ∘ lift ∘ fs ∘ lower)

 ℰ!⟨Lift⟩ : ℰ! A → ℰ! (Lift b A)
 ℰ!⟨Lift⟩ xs .fst = map lift (xs .fst)
 ℰ!⟨Lift⟩ xs .snd x = cong-∈ lift (xs .fst) (xs .snd (x .lower))

 ℰ!⟨≡⟩ : (x y : A) → ℰ! A → ℰ! (x ≡ y)
 ℰ!⟨≡⟩ x y e with ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun e) x y
 ℰ!⟨≡⟩ x y e | yes p = (p ∷ []) , λ q → (f0 , Discrete→isSet (ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun e)) x y p q)
 ℰ!⟨≡⟩ x y e | no ¬p = [] , (⊥-elim ∘ ¬p)
