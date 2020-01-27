{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude

module Cardinality.Finite.Cardinal.Category {ℓ : Level} where

open import Cardinality.Finite.Cardinal
open import HITs.PropositionalTruncation
open import Data.Sigma.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Categories
open import Cubical.Foundations.Univalence
open import Categories.Product
open import Categories.Exponential
open import Data.Fin
open import Cardinality.Finite.ManifestBishop

𝒞⇒isSet : 𝒞 A → isSet A
𝒞⇒isSet = Discrete→isSet ∘ 𝒞⇒Discrete

finSetPreCategory : PreCategory (ℓsuc ℓ) ℓ
finSetPreCategory .PreCategory.Ob = Σ (Type ℓ) 𝒞
finSetPreCategory .PreCategory.Hom (X , _) (Y , _) = X → Y
finSetPreCategory .PreCategory.Id = id
finSetPreCategory .PreCategory.Comp f g = f ∘ g
finSetPreCategory .PreCategory.assoc-Comp _ _ _ = refl
finSetPreCategory .PreCategory.Comp-Id _ = refl
finSetPreCategory .PreCategory.Id-Comp _ = refl
finSetPreCategory .PreCategory.Hom-Set {X} {Y} = hLevelPi 2 λ _ → Discrete→isSet (𝒞⇒Discrete (Y .snd))

open PreCategory finSetPreCategory

iso-iso : (X ≅ Y) ⇔ (fst X ⇔ fst Y)
iso-iso .fun (f , g , f∘g , g∘f) = iso f g (λ x i → g∘f i x) (λ x i → f∘g i x)
iso-iso .inv (iso f g g∘f f∘g) = f , g  , (λ i x → f∘g x i) , (λ i x → g∘f x i)
iso-iso .rightInv _ = refl
iso-iso .leftInv  _ = refl

finSetCategory : Category (ℓsuc ℓ) ℓ
finSetCategory .Category.preCategory = finSetPreCategory
finSetCategory .Category.univalent {X} {Y} =
  ≃ΣProp≡ (λ _ → squash) ⟨ trans-≃ ⟩
  univalence ⟨ trans-≃ ⟩
  isoToEquiv (
  sym-⇔ (iso⇔equiv (Discrete→isSet (𝒞⇒Discrete (X .snd)))) ⟨ trans-⇔ ⟩
  sym-⇔ (iso-iso {X} {Y}))

finSetHasProducts : HasProducts finSetCategory
finSetHasProducts .HasProducts.product X Y .Product.obj = X .fst × Y .fst , X .snd ∥×∥ Y .snd
finSetHasProducts .HasProducts.product X Y .Product.proj₁ = fst
finSetHasProducts .HasProducts.product X Y .Product.proj₂ = snd
finSetHasProducts .HasProducts.product X Y .Product.ump f g .fst z = f z , g z
finSetHasProducts .HasProducts.product X Y .Product.ump f g .snd .fst .fst = refl
finSetHasProducts .HasProducts.product X Y .Product.ump f g .snd .fst .snd = refl
finSetHasProducts .HasProducts.product X Y .Product.ump f g .snd .snd (f≡ , g≡) i x = f≡ (~ i) x , g≡ (~ i) x

finSetHasExp : HasExponentials finSetCategory finSetHasProducts
finSetHasExp X Y .Exponential.obj = (X .fst → Y .fst) , (X .snd ∥→∥ Y .snd)
finSetHasExp X Y .Exponential.eval (f , x) = f x
finSetHasExp X Y .Exponential.uniq X₁ f .fst = curry f
finSetHasExp X Y .Exponential.uniq X₁ f .snd .fst = refl
finSetHasExp X Y .Exponential.uniq X₁ f .snd .snd x = cong curry (sym x)

open import Categories.Pullback
open import Cardinality.Finite.SplitEnumerable using (ℰ!⟨Lift⟩; ℰ!⟨⊤⟩; ℰ!⟨⊥⟩)


finSetHasPullbacks : HasPullbacks finSetCategory
finSetHasPullbacks {X = X} {Y = Y} {Z = Z} f g .Pullback.P = ∃[ ab ] (f (fst ab) ≡ g (snd ab)) , ((X .snd ∥×∥ Y .snd) ∥Σ∥ λ _ → 𝒞⟨≡⟩ _ _ (Z .snd))
finSetHasPullbacks f g .Pullback.p₁ ((x , _) , _) = x
finSetHasPullbacks f g .Pullback.p₂ ((_ , y) , _) = y
finSetHasPullbacks f g .Pullback.commute = funExt snd
finSetHasPullbacks f g .Pullback.ump {A = A} h₁ h₂ p .fst x = (h₁ x , h₂ x) , λ i → p i x
finSetHasPullbacks f g .Pullback.ump {A = A} h₁ h₂ p .snd .fst .fst = refl
finSetHasPullbacks f g .Pullback.ump {A = A} h₁ h₂ p .snd .fst .snd = refl
finSetHasPullbacks {Z = Z} f g .Pullback.ump {A = A} h₁ h₂ p .snd .snd {i} (p₁e , p₂e) = funExt (λ x → ΣProp≡ (λ _ →  𝒞⇒isSet (Z .snd) _ _) λ j → p₁e (~ j) x , p₂e (~ j) x)

finSetTerminal : Terminal
finSetTerminal .fst = Lift _ ⊤ , ∣ ℰ!⇒ℬ (ℰ!⟨Lift⟩ ℰ!⟨⊤⟩) ∣
finSetTerminal .snd .fst x .lower = tt
finSetTerminal .snd .snd y = funExt λ _ → refl

finSetInitial : Initial
finSetInitial .fst = Lift _ ⊥ , ∣ ℰ!⇒ℬ (ℰ!⟨Lift⟩ ℰ!⟨⊥⟩) ∣
finSetInitial .snd .fst ()
finSetInitial .snd .snd y i ()

open import HITs.PropositionalTruncation
open import Categories.Coequalizer

∃!′ : (A : Type a) → (A → Type b) → Type (a ℓ⊔ b)
∃!′ A P = ∥ Σ A P ∥ Prelude.× AtMostOne P

lemma23 : ∀ {p} {P : A → hProp p} → ∃!′ A (fst ∘ P) → Σ A (fst ∘ P)
lemma23 {P = P} (x , y) = recPropTrunc (λ xs ys → ΣProp≡ (snd ∘ P) (y (xs .fst) (ys .fst) (xs .snd) (ys .snd))) id x

module _ {A : Type a} {P : A → Type b} (R : ∀ x → P x → hProp c) where
  uniqueChoice : (Π[ x ⦂ A ] (∃!′ (P x) (λ u → R x u .fst))) →
                 Σ[ f ⦂ Π[ x ⦂ A ] P x ] Π[ x ⦂ A ] (R x (f x) .fst)
  uniqueChoice H = fst ∘ mid , snd ∘ mid
    where
    mid : Π[ x ⦂ A ] Σ[ u ⦂ P x ] (R x u .fst)
    mid x = lemma23 {P = R x} (H x)

open import HITs.PropositionalTruncation.Sugar
open import Data.List using (_∷_; [])
open import Cardinality.Finite.SplitEnumerable.Search using (ℰ!⟨fib⟩)

module CoeqProofs {X Y : Ob} (f : X ⟶ Y) where
  KernelPair : Pullback finSetCategory {X = X} {Z = Y} {Y = X} f f
  KernelPair = finSetHasPullbacks f f

  Im : Ob
  Im = ∃[ b ] ∥ fiber f b ∥ , (Y .snd ∥Σ∥ λ x → do cx ← X .snd ; cy ← Y .snd ; ∣ ℰ!⇒ℬ (ℰ!⟨fib⟩ f _ (ℬ⇒ℰ! cx) (ℬ⇒ℰ! cy)) ∣)

  im : X ⟶ Im
  im x = f x , ∣ x , refl ∣

  open Pullback KernelPair

  lem : ∀ {H : Ob} (h : X ⟶ H) → h ∘ p₁ ≡ h ∘ p₂ → Σ[ f ⦂ (Im ⟶ H) ] Π[ x ⦂ Im .fst ] (∀ y → im y ≡ x → h y ≡ f x)
  lem {H = H} h eq = uniqueChoice R prf
    where
    R : Im .fst → H .fst → hProp _
    R w x .fst = ∀ y → im y ≡ w → h y ≡ x
    R w x .snd = hLevelPi 1 λ _ → hLevelPi 1 λ _ → 𝒞⇒isSet (H .snd) _ _

    prf : Π[ x ⦂ Im .fst ] ∃!′ (H .fst) (λ u → ∀ y → im y ≡ x → h y ≡ u)
    prf (xy , p) .fst = (λ { (z , r) → h z , λ y imy≡xyp → cong (_$ ((y , z) , cong fst imy≡xyp ; sym r)) eq }) ∥$∥ p
    prf (xy , p) .snd x₁ x₂ Px₁ Px₂ = recPropTrunc (𝒞⇒isSet (H .snd) x₁ x₂) (λ { (z , zs) → sym (Px₁ z (ΣProp≡ (λ _ → squash) zs)) ; Px₂ z (ΣProp≡ (λ _ → squash) zs) } ) p

  lem₂ : ∀ (H : Ob) (h : X ⟶ H) (i : Im ⟶ H) (x : Im .fst) (hi : h ≡ i ∘ im) (eq : h ∘ p₁ ≡ h ∘ p₂) → i x ≡ lem {H = H} h eq .fst x
  lem₂ H h i x hi eq = recPropTrunc (𝒞⇒isSet (H .snd) _ _) (λ { (y , ys) → (cong i (ΣProp≡ (λ _ → squash) (sym ys)) ; sym (cong (_$ y) hi)) ; lem {H = H} h eq .snd x y (ΣProp≡ (λ _ → squash) ys) }) (x .snd)

  finSetCoeq : Coequalizer finSetCategory {X = P} {Y = X} p₁ p₂
  finSetCoeq .Coequalizer.obj = Im
  finSetCoeq .Coequalizer.arr = im
  finSetCoeq .Coequalizer.equality = funExt λ x → ΣProp≡ (λ _ → squash) λ i → commute i x
  finSetCoeq .Coequalizer.coequalize {H = H} {h = h} eq = lem {H = H} h eq .fst
  finSetCoeq .Coequalizer.universal {H = H} {h = h} {eq = eq} = funExt λ x → lem {H = H} h eq .snd (im x) x refl
  finSetCoeq .Coequalizer.unique {H = H} {h = h} {i = i} {eq = eq} prf = funExt λ x → lem₂ H h i x prf eq
open CoeqProofs public using (finSetCoeq)

module PullbackSurjProofs {X Y : Ob} (f : X ⟶ Y) (fSurj : Surjective f) where
  KernelPair : Pullback finSetCategory {X = X} {Z = Y} {Y = X} f f
  KernelPair = finSetHasPullbacks f f

  open Pullback KernelPair

  p₁surj : Surjective p₁
  p₁surj y = ∣ ((y , y) , refl) , refl ∣

  p₂surj : Surjective p₂
  p₂surj y = ∣ ((y , y) , refl) , refl ∣
