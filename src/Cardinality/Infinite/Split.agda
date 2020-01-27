{-# OPTIONS --cubical --safe #-}

module Cardinality.Infinite.Split where

open import Prelude
open import Data.List.Kleene
open import Data.Fin
import Data.Nat as ℕ
open import Data.Nat using (_+_)
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Prelude using (J)
import Data.List.Kleene.Membership as Kleene
open import Codata.Stream
open import Data.Sigma.Properties

private
  variable
    u : Level
    U : A → Type u
    s : Level
    S : ℕ → Type s

ℰ! : Type a → Type a
ℰ! A = Σ[ xs ⦂ Stream A ] Π[ x ⦂ A ] x ∈ xs

ℰ!⇔ℕ↠! : ℰ! A ≡ (ℕ ↠! A)
ℰ!⇔ℕ↠! = refl

infixl 6 _*_ _*⋆_[_]
_*_ : Stream A → (∀ x → Stream (U x)) → Stream (Σ A U ⁺)
_*⋆_[_] : Stream A → (∀ x → Stream (U x)) → Stream (Σ A U ⋆)
cantor : Stream A → (∀ x → Stream (U x)) → Stream (Σ A U)
cantor xs ys = concat (xs * ys)

xs *⋆ ys [ zero   ] = []
xs *⋆ ys [ suc n  ] = ∹ (xs * ys) n

(xs * ys) n .head  = x , ys x n where x = xs 0
(xs * ys) n .tail  = (xs ∘ suc) *⋆ ys [ n ]

*-cover : ∀ (x : A) xs (y : U x) (ys : ∀ x → Stream (U x)) → x ∈ xs → y ∈ ys x → (x , y) ∈² xs * ys
*-cover {U = U} x xs y ys (n , x∈xs) (m , y∈ys) = (n + m) , lemma xs n x∈xs
  where
  lemma : ∀ xs n → xs n ≡ x → (x , y) Kleene.∈⁺ (xs * ys) (n + m)
  lemma xs zero    x∈xs .fst = f0
  lemma xs zero    x∈xs .snd i .fst = x∈xs i
  lemma xs zero    x∈xs .snd i .snd = J (λ z z≡ → PathP (λ j → U (sym z≡ j)) (ys z m) y) y∈ys (sym x∈xs) i
  lemma xs (suc n) x∈xs = let i , p = lemma (xs ∘ suc) n x∈xs in fs i , p

_|Σ|_ : ℰ! A → (∀ x → ℰ! (U x)) → ℰ! (Σ A U)
(xs |Σ| ys) .fst = cantor (xs .fst) (fst ∘ ys)
(xs |Σ| ys) .snd (x , y) =
  concat-∈
    (x , y)
    (xs .fst * (fst ∘ ys))
    (*-cover x (xs .fst) y (fst ∘ ys) (xs .snd x) (ys x .snd y))

open import Data.Nat using (_+_)

infixl 6 _∔_
_∔_ : ℕ → ℕ → ℕ
zero ∔ m = m
suc n ∔ m = n ∔ suc m

∔-suc : ∀ n m → suc n ∔ m ≡ suc (n ∔ m)
∔-suc zero    m = refl
∔-suc (suc n) m = ∔-suc n (suc m)

∔0 : ∀ n → n ∔ zero ≡ n
∔0 zero    = refl
∔0 (suc n) = ∔-suc n 0 ; cong suc (∔0 n)

module _ (xs : Stream A) where
  mutual
    star⁺ : (A ⋆ → B) → B ⋆ → Stream (B ⁺)
    star⁺ k ks zero    = k [] & ks
    star⁺ k ks (suc i) = plus⁺ zero (k ∘ ∹_) ks i

    plus⋆ : ℕ → (A ⁺ → B) → B ⋆ → Stream (B ⋆)
    plus⋆ n k ks zero    = ks
    plus⋆ n k ks (suc i) = ∹ plus⁺ n k ks i

    plus⁺ : ℕ → (A ⁺ → B) → B ⋆ → Stream (B ⁺)
    plus⁺ n k ks i = star⁺ (k ∘ (xs n &_)) (plus⋆ (suc n) k ks i) i

  star : Stream (A ⋆)
  star = concat (star⁺ id [])

  plus : Stream (A ⁺)
  plus = concat (plus⁺ zero id [])

  module _ (cover : ∀ x → x ∈ xs) where
    dist : A ⋆ → ℕ
    dist = foldr⋆ (λ y ys → suc (cover y .fst + ys)) zero

    mutual
      star⁺-cover : (k : A ⋆ → B) → (ks : B ⋆) → ∀ x → k x Kleene.∈⁺ star⁺ k ks (dist x)
      star⁺-cover k ks [] = f0 , refl
      star⁺-cover k ks (∹ x ) = plus⁺-cover (k ∘ ∹_) ks x

      plus⁺-cover : ∀ (k : A ⁺ → B) ks → ∀ x → k x Kleene.∈⁺ plus⁺ zero k ks (cover (head x) .fst + dist (tail x))
      plus⁺-cover k ks (x & xxs) =
        let n , p = cover x
            m , q = plus⁺-dist n (k ) ks xxs
            z = m , q ; cong (k ∘ (_& xxs)) p
        in plus⁺-shift zero (dist xxs) n k ks (x & xxs) (subst (λ s → k (x & xxs) Kleene.∈⁺ plus⁺ s k ks (dist xxs)) (sym (∔0 (cover x .fst))) z)

      plus⁺-dist : ∀ n (k : A ⁺ → B) ks → ∀ xxs → k (xs n & xxs) Kleene.∈⁺ plus⁺ n k ks (dist xxs)
      plus⁺-dist n k ks xxs = star⁺-cover (k ∘ _&_ (xs n)) (plus⋆ (suc n) k ks (dist xxs)) xxs

      plus⁺-run : ∀ n i (k : A ⁺ → B) ks → ∀ xxs → xxs Kleene.∈⋆ ks → xxs Kleene.∈⁺ plus⁺ n k ks i
      plus⁺-run n zero    k ks xxs (m , p) = fs m , p
      plus⁺-run n (suc i) k ks xxs =
        plus⁺-run zero i (k ∘ (xs n &_) ∘ ∹_) (plus⋆ (suc n) k ks (suc i)) xxs ∘
        plus⁺-run (suc n) i k ks xxs

      plus⁺-shift : ∀ i d n (k : A ⁺ → B) (ks : B ⋆) → ∀ xxs → k xxs Kleene.∈⁺ plus⁺ (n ∔ i) k ks d → k xxs Kleene.∈⁺ plus⁺ i k ks (n + d)
      plus⁺-shift i d zero    k ks xxs p = p
      plus⁺-shift i d (suc n) k ks xxs p = plus⁺-run zero (n + d) (λ z → k (xs i & ∹ z)) (∹ plus⁺ (suc i) k ks (n + d)) (k xxs) (plus⁺-shift (suc i) d n k ks xxs p)

    star-cover : ∀ x → x ∈ star
    star-cover x = concat-∈ x (star⁺ id []) (dist x , star⁺-cover id [] x)

    plus-cover : ∀ x → x ∈ plus
    plus-cover x = concat-∈ x (plus⁺ zero id []) (cover (head x) .fst + dist (tail x) , plus⁺-cover id [] x)

|star| : ℰ! A → ℰ! (A ⋆)
|star| xs .fst = star (xs .fst)
|star| xs .snd = star-cover (xs .fst) (xs .snd)

|plus| : ℰ! A → ℰ! (A ⁺)
|plus| xs .fst = plus (xs .fst)
|plus| xs .snd = plus-cover (xs .fst) (xs .snd)

open import Data.Bool using (not; bool)

x≢¬x : ∀ x → x ≢ not x
x≢¬x false p = subst (bool ⊤ ⊥) p tt
x≢¬x true  p = subst (bool ⊥ ⊤) p tt

cantor-diag : ¬ (ℰ! (Stream Bool))
cantor-diag (sup , cov) = let n , p = cov (λ n → not (sup n n)) in x≢¬x _ (cong (_$ n) p)

ℰ : Type a → Type a
ℰ A = ∥ ℰ! A ∥

open import Function.Surjective.Properties
open import Data.Nat.Properties using (discreteℕ)
open import HITs.PropositionalTruncation
open import Relation.Nullary.Discrete.Properties

ℰ!⇒Discrete : ℰ! A → Discrete A
ℰ!⇒Discrete xs = Discrete↠!A⇒Discrete⟨A⟩ xs discreteℕ

ℰ⇒Discrete : ℰ A → Discrete A
ℰ⇒Discrete = recPropTrunc isPropDiscrete ℰ!⇒Discrete
