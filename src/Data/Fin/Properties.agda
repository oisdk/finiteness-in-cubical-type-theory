{-# OPTIONS --cubical --safe #-}

module Data.Fin.Properties where

open import Prelude
open import Data.Fin.Base
import Data.Nat.Properties as ℕ
open import Data.Nat.Properties using (+-comm)
open import Data.Nat
open import Function.Injective
open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_)

private
  variable
    n m : ℕ

FinToℕ : Fin n → ℕ
FinToℕ {n = suc n} f0     = zero
FinToℕ {n = suc n} (fs x)  = suc (FinToℕ x)

FinToℕ-injective : ∀ {k} {m n : Fin k} → FinToℕ m ≡ FinToℕ n → m ≡ n
FinToℕ-injective {suc k} {f0}  {f0}  _ = refl
FinToℕ-injective {suc k} {f0}  {fs x} p = ⊥-elim (ℕ.znots p)
FinToℕ-injective {suc k} {fs m} {f0}  p = ⊥-elim (ℕ.snotz p)
FinToℕ-injective {suc k} {fs m} {fs x} p = cong fs (FinToℕ-injective (ℕ.injSuc p))

pred : Fin (suc n) → Fin (suc (ℕ.pred n))
pred f0 = f0
pred {n = suc n} (fs m) = m

discreteFin : ∀ {k} → Discrete (Fin k)
discreteFin {k = suc _} f0 f0 = yes refl
discreteFin {k = suc _} f0 (fs fk) = no (ℕ.znots ∘ cong FinToℕ)
discreteFin {k = suc _} (fs fj) f0 = no (ℕ.snotz ∘ cong FinToℕ)
discreteFin {k = suc _} (fs fj) (fs fk) =
  ⟦yes cong fs ,no cong (λ { f0 → fk ; (fs x) → x}) ⟧ (discreteFin fj fk)

isSetFin : isSet (Fin n)
isSetFin = Discrete→isSet discreteFin

FinFromℕ : (n m : ℕ) → T (n <ᵇ m) → Fin m
FinFromℕ zero (suc m) p = f0
FinFromℕ (suc n) (suc m) p = fs (FinFromℕ n m p)

infix 4 _≢ᶠ_ _≡ᶠ_
_≢ᶠ_ _≡ᶠ_ : Fin n → Fin n → Type _
n ≢ᶠ m = T (not (discreteFin n m .does))
n ≡ᶠ m = T (discreteFin n m .does)

_F↣_ : ℕ → ℕ → Type₀
n F↣ m = Σ[ f ⦂ (Fin n → Fin m) ] ∀ {x y} → x ≢ᶠ y → f x ≢ᶠ f y

shift : (x y : Fin (suc n)) → x ≢ᶠ y → Fin n
shift          f0     (fs y)  x≢y = y
shift {suc _}  (fs x)  f0     x≢y = f0
shift {suc _}  (fs x)  (fs y)  x≢y = fs (shift x y x≢y)

shift-inj : ∀ (x y z : Fin (suc n)) x≢y x≢z → y ≢ᶠ z → shift x y x≢y ≢ᶠ shift x z x≢z
shift-inj          f0     (fs y)  (fs z)  x≢y x≢z x+y≢x+z = x+y≢x+z
shift-inj {suc _}  (fs x)  f0     (fs z)  x≢y x≢z x+y≢x+z = tt
shift-inj {suc _}  (fs x)  (fs y)  f0     x≢y x≢z x+y≢x+z = tt
shift-inj {suc _}  (fs x)  (fs y)  (fs z)  x≢y x≢z x+y≢x+z = shift-inj x y z x≢y x≢z x+y≢x+z

shrink : suc n F↣ suc m → n F↣ m
shrink (f , inj) .fst  x  = shift (f f0) (f (fs x)) (inj tt)
shrink (f , inj) .snd  p  = shift-inj (f f0) (f (fs _)) (f (fs _)) (inj tt) (inj tt) (inj p)

¬plus-inj : ∀ n m → ¬ (suc (n + m) F↣ m)
¬plus-inj zero     zero     (f , _)  = f f0
¬plus-inj zero     (suc m)  inj      = ¬plus-inj zero m (shrink inj)
¬plus-inj (suc n)  m        (f , p)  = ¬plus-inj n m (f ∘ fs , p)

toFin-inj : (Fin n ↣ Fin m) → n F↣ m
toFin-inj f .fst = f .fst
toFin-inj (f , inj) .snd {x} {y} x≢ᶠy with discreteFin x y | discreteFin (f x) (f y)
... | no ¬p  | yes p  = ¬p (inj _ _ p)
... | no _   | no _   = tt

n≢sn+m : ∀ n m → Fin n ≢ Fin (suc (n + m))
n≢sn+m n m n≡m =
  ¬plus-inj m n
    (toFin-inj
      (subst
        (_↣ Fin n)
        (n≡m ; cong (Fin ∘ suc) (+-comm n m))
        refl-↣))

Fin-inj : Injective Fin
Fin-inj n m eq with compare n m
... | equal _        = refl
... | less     n  k  = ⊥-elim (n≢sn+m n k eq)
... | greater  m  k  = ⊥-elim (n≢sn+m m k (sym eq))
