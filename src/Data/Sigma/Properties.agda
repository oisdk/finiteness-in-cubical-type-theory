{-# OPTIONS --cubical --safe #-}

module Data.Sigma.Properties where

open import Prelude
open import Cubical.Foundations.HLevels using (ΣProp≡; isOfHLevelΣ) public

reassoc : {A : Type a} {B : A → Type b} {C : Σ A B → Type c} → Σ (Σ A B) C ⇔ (Σ[ x ⦂ A ] Σ[ y ⦂ B x ] C (x , y))
reassoc .fun ((x , y) , z) = x , (y , z)
reassoc .inv (x , (y , z)) = (x , y) , z
reassoc .rightInv _ = refl
reassoc .leftInv  _ = refl

≃ΣProp≡ : ∀ {A : Type a} {u} {U : A → Type u} → ((x : A) → isProp (U x)) → {p q : Σ A U} → (p ≡ q) ≃ (fst p ≡ fst q)
≃ΣProp≡ {A = A} {U = U} pA {p} {q} = isoToEquiv (iso to fro (λ _ → refl) (J Jt Jp))
  where
  to : {p q : Σ A U} → p ≡ q → fst p ≡ fst q
  to = cong fst

  fro : ∀ {p q} → fst p ≡ fst q → p ≡ q
  fro = ΣProp≡ pA

  Jt : (q : Σ A U) → p ≡ q → Type _
  Jt q q≡ = fro (to q≡) ≡ q≡

  Jp : Jt p refl
  Jp i j .fst = p .fst
  Jp i j .snd = isProp→isSet (pA (p .fst)) (p .snd) (p .snd) (λ k → fro {p} {p} (to (refl {x = p})) k .snd) refl i j
