{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.Cardinal where

open import Prelude
open import Cardinality.Finite.ManifestBishop
open import Cardinality.Finite.ManifestBishop.Inductive
open import Cardinality.Finite.ManifestBishop.Isomorphism
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Isomorphism

open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

open import Relation.Nullary.Discrete.Properties

open import Data.Fin

𝒞 : Type a → Type a
𝒞 A = ∥ ℬ A ∥

𝒞≃Fin≃ : 𝒞 A ≃ ∥ Σ[ n ⦂ ℕ ] (Fin n ≃ A) ∥
𝒞≃Fin≃ = isoToEquiv (iso (ℬ⇔Fin≃ .fun ∘ 𝕃⇔ℒ⟨ℬ⟩ .fun ∥$∥_) (𝕃⇔ℒ⟨ℬ⟩ .inv ∘ ℬ⇔Fin≃ .inv ∥$∥_) (λ _ → squash _ _) λ _ → squash _ _)

ℬ⇒𝒞 : ℬ A → 𝒞 A
ℬ⇒𝒞 = ∣_∣

private
  variable
    u : Level
    U : A → Type u

𝒞⇒Choice : 𝒞 A → Π[ x ⦂ A ] ∥ U x ∥ → ∥ Π[ x ⦂ A ] U x ∥
𝒞⇒Choice ca p = ca >>= flip ℬ⇒Choice p

𝒞⟨⊥⟩ : 𝒞 ⊥
𝒞⟨⊥⟩ = ∣ ℰ!⇒ℬ ℰ!⟨⊥⟩ ∣

𝒞⟨⊤⟩ : 𝒞 ⊤
𝒞⟨⊤⟩ = ∣ ℰ!⇒ℬ ℰ!⟨⊤⟩ ∣

𝒞⟨Bool⟩ : 𝒞 Bool
𝒞⟨Bool⟩ = ∣ ℰ!⇒ℬ ℰ!⟨2⟩ ∣


infixr 3 _∥Σ∥_
_∥Σ∥_ : 𝒞 A → (∀ x → 𝒞 (U x)) → 𝒞 (Σ A U)
xs ∥Σ∥ ys = do
  x ← xs
  y ← ℬ⇒Choice x ys
  ∣ ℰ!⇒ℬ (ℬ⇒ℰ! x |Σ| (ℬ⇒ℰ! ∘ y)) ∣

_∥⊎∥_ : 𝒞 A → 𝒞 B → 𝒞 (A ⊎ B)
xs ∥⊎∥ ys = do
  x ← xs
  y ← ys
  ∣ ℰ!⇒ℬ (ℬ⇒ℰ! x |⊎| ℬ⇒ℰ! y) ∣

_∥Π∥_ : 𝒞 A → (∀ x → 𝒞 (U x)) → 𝒞 (Π A U)
xs ∥Π∥ ys = do
  x ← xs
  y ← ℬ⇒Choice x ys
  ∣ ℰ!⇒ℬ (ℬ⇒ℰ! x |Π| (ℬ⇒ℰ! ∘ y)) ∣

_∥→∥_ : 𝒞 A → 𝒞 B → 𝒞 (A → B)
xs ∥→∥ ys = xs ∥Π∥ const ys

_∥×∥_ : 𝒞 A → 𝒞 B → 𝒞 (A × B)
xs ∥×∥ ys = xs ∥Σ∥ const ys


𝒞⇒Discrete : 𝒞 A → Discrete A
𝒞⇒Discrete = recPropTrunc isPropDiscrete (ℰ!⇒Discrete ∘ 𝕃⇔ℒ⟨ℰ!⟩ .fun ∘ ℬ⇒ℰ!)

open import Data.Sigma.Properties
open import Data.Fin.Properties using (Fin-inj)
open import Data.Nat.Properties using (isSetℕ)
open import Cubical.Foundations.HLevels

cardinality : ∥ ∃[ n ] (Fin n ≃ A) ∥ → ∃[ n ] ∥ Fin n ≃ A ∥
cardinality {A = A} = recPropTrunc→Set (isOfHLevelΣ 2 isSetℕ λ _ → isProp→isSet squash) alg const-alg
  where
  alg : Σ[ n ⦂ ℕ ] (Fin n ≃ A) → Σ[ n ⦂ ℕ ] ∥ Fin n ≃ A ∥
  alg (n , f≃A) = n , ∣ f≃A ∣

  const-alg : (x y : ∃[ n ] (Fin n ≃ A)) → alg x ≡ alg y
  const-alg (n , x) (m , y) =
    ΣProp≡
      (λ _ → squash)
      {n , ∣ x ∣} {m , ∣ y ∣}
      (Fin-inj n m (ua (x ⟨ trans-≃ ⟩ (sym-≃ y))))

# : 𝒞 A → ℕ
# = fst ∘ cardinality ∘ _∥$∥_ (ℬ⇔Fin≃ .fun ∘ 𝕃⇔ℒ⟨ℬ⟩ .fun)

open import Data.List.Filter
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Relation.Nullary.Decidable.Logic

filter-subobject : ∀ {p} {P : A → Type p} (isPropP : ∀ x → isProp (P x)) (P? : ∀ x → Dec (P x)) →
                   ℰ! A → ℰ! (Σ[ x ⦂ A ] (P x))
filter-subobject isPropP P? xs .fst = filter P? (xs .fst)
filter-subobject isPropP P? xs .snd (x , v) = filter-preserves isPropP P? (xs .fst) x v (xs .snd x)

module _ {a b} {A : Type a} {B : Type b} where
 _∥⇔∥_ : 𝒞 A → 𝒞 B → 𝒞 (A ⇔ B)
 xs ∥⇔∥ ys = subst 𝒞 (isoToPath form) p
   where
   𝒞⟨f⟩ : 𝒞 (A → B)
   𝒞⟨f⟩ = xs ∥→∥ ys

   𝒞⟨g⟩ : 𝒞 (B → A)
   𝒞⟨g⟩ = ys ∥→∥ xs

   p : 𝒞 (Σ[ fg ⦂ ((A → B) × (B → A)) ] (((fg .fst ∘ fg .snd) ≡ id) × ((fg .snd ∘ fg .fst) ≡ id)))
   p = ℰ!⇒ℬ ∘ filter-subobject
     (λ fg → isOfHLevelΣ 1 (Discrete→isSet (𝒞⇒Discrete (ys ∥→∥ ys)) _ _) λ _ → (Discrete→isSet (𝒞⇒Discrete (xs ∥→∥ xs)) _ _))
     (λ { (f , g) → 𝒞⇒Discrete (ys ∥→∥ ys) (f ∘ g) id && 𝒞⇒Discrete (xs ∥→∥ xs) (g ∘ f) id}) ∘ ℬ⇒ℰ!
     ∥$∥ (𝒞⟨f⟩ ∥×∥ 𝒞⟨g⟩)

   form : (Σ[ fg ⦂ ((A → B) × (B → A)) ] (((fg .fst ∘ fg .snd) ≡ id) × ((fg .snd ∘ fg .fst) ≡ id))) ⇔ (A ⇔ B)
   form .fun ((f , g) , (leftInv , rightInv)) = iso f g (λ x i → leftInv i x) (λ x i → rightInv i x)
   form .inv (iso f g leftInv rightInv) = ((f , g) , ((λ i x → leftInv x i) , (λ i x → rightInv x i)))
   form .rightInv _ = refl
   form .leftInv  _ = refl

open import Relation.Binary
open import Data.List.Relation.Binary.Permutation

perm-ℬ : (xs ys : ℬ A) → xs .fst ↭ ys .fst
perm-ℬ xs ys  x .fun  _    = ys  .snd x .fst
perm-ℬ xs ys  x .inv  _    = xs  .snd x .fst
perm-ℬ xs ys  x .rightInv  = ys  .snd x .snd
perm-ℬ xs ys  x .leftInv   = xs  .snd x .snd

module _ {e r} {E : Type e} (totalOrder : TotalOrder E r) where
  open import Data.List.Sort totalOrder
  open import Cubical.HITs.PropositionalTruncation using (recPropTrunc→Set)
  open import Data.Sigma.Properties
  open import Cardinality.Finite.ManifestBishop using (ℰ!⇒ℬ)
  open import Cardinality.Finite.ManifestEnumerable.Inductive
  open import Cardinality.Finite.ManifestEnumerable

  𝒞⇒ℬ : 𝒞 E → ℬ E
  𝒞⇒ℬ xs = (ℰ!⇒ℬ ∘ ℰ⇒ℰ! discreteE ∘ recPropTrunc→Set (isSet⟨ℰ⟩ (Discrete→isSet discreteE)) alg const-alg) xs
    where
    discreteE = 𝒞⇒Discrete xs

    alg : ℬ E → ℰ E
    alg xs .fst = sort (xs .fst)
    alg xs .snd x = ∣ sort-perm (xs .fst) x .inv (xs .snd x .fst) ∣

    const-alg : (xs ys : ℬ E) → alg xs ≡ alg ys
    const-alg xs ys =
      ΣProp≡
        (λ _ → hLevelPi 1 (λ _ → squash))
        (perm-invar (xs .fst) (ys .fst) (perm-ℬ xs ys))

open import Cardinality.Finite.SplitEnumerable using (ℰ!⟨≡⟩)

𝒞⟨≡⟩ : (x y : A) → 𝒞 A → 𝒞 (x ≡ y)
𝒞⟨≡⟩ x y ca = ℰ!⇒ℬ ∘ ℰ!⟨≡⟩ x y ∘ ℬ⇒ℰ! ∥$∥ ca
