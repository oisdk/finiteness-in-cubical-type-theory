{-# OPTIONS --cubical --safe #-}

module README where

--------------------------------------------------------------------------------
-- Section 1: Introduction
--------------------------------------------------------------------------------

-- 0, 1, and 2 types
import Data.Empty using (⊥)
import Data.Unit  using (⊤)
import Data.Bool  using (Bool)

-- Dependent Sum and Product
import Data.Sigma using (Σ)
import Data.Pi    using (Π)

-- Disjoint Union
import Data.Sum using (_⊎_)
import Data.Sum.Properties using (sumAsSigma)

-- Definition 1: Path types
import Path using (_≡_)

-- Definition 2: Homotopy Levels
import HLevels using (isContr; isProp; isSet)

-- Definition 3: Fibres
import Function.Fiber using (fiber)

-- Definition 4: Equivalences
import Equiv using (isEquiv; _≃_)

-- Definition 5: Decidable
import Relation.Nullary.Decidable using (Dec)

-- Definition 6: Discrete
import Relation.Nullary.Discrete using (Discrete)
import Relation.Nullary.Discrete.Properties using (Discrete→isSet)

-- Definition 8: Propositional Truncation
import HITs.PropositionalTruncation using (∥_∥)
import HITs.PropositionalTruncation using (recPropTrunc; recPropTrunc→Set)

--------------------------------------------------------------------------------
-- Section 2: Finiteness Predicates
--------------------------------------------------------------------------------

-- Definition 9: Split Enumerability
import Cardinality.Finite.SplitEnumerable.Container using (ℰ!)

-- Container based definition is isomophic to inductive
import Cardinality.Finite.SplitEnumerable.Isomorphism using (𝕃⇔ℒ⟨ℰ!⟩)

-- Definition 10: Container
import Container using (Container; ⟦_⟧)

-- Definition 11: List
import Container.List using (List)

-- Definition 12: Fin
import Data.Fin.Base using (Fin)

-- Definition 13: Surjections
import Function.Surjective using (_↠!_; _↠_)

-- Lemma 1
import Cardinality.Finite.SplitEnumerable using (ℰ!⇔Fin↠!)

-- Lemma 2
import Function.Surjective.Properties using (Discrete↠!A⇒Discrete⟨A⟩)

-- Lemma 3
import Cardinality.Finite.SplitEnumerable using (ℰ!⇒Discrete)

-- Definition 14: Manifest Bishop Finiteness
import Cardinality.Finite.ManifestBishop.Container using (ℬ)

-- Container based definition is isomophic to inductive
import Cardinality.Finite.ManifestBishop.Isomorphism using (𝕃⇔ℒ⟨ℬ⟩)

-- Definition 15: Unique Membership
import Container.Membership using (_∈!_)

-- Lemma 4
import Cardinality.Finite.ManifestBishop using (ℬ⇔Fin≃)

-- Definition 16: Cardinal Finiteness
import Cardinality.Finite.Cardinal using (𝒞; 𝒞≃Fin≃)

-- Lemma 5
import Cardinality.Finite.Cardinal using (cardinality)

-- Lemma 6
import Cardinality.Finite.Cardinal using (𝒞⇒Discrete)

-- Definition 17: Manifest Enumerability
import Cardinality.Finite.ManifestEnumerable.Container using (ℰ)

-- Container based definition is isomorphic to inductive
import Cardinality.Finite.ManifestEnumerable.Isomorphism using (𝕃⇔ℒ⟨ℰ⟩)

-- Lemma 7
import Cardinality.Finite.ManifestEnumerable using (ℰ⇔Fin↠)

-- Definition 18: S¹
open import Cubical.HITs.S1 using (S¹)

-- Lemma 8
import Cardinality.Finite.ManifestEnumerable using (ℰ⟨S¹⟩)

-- Definition 19: Kuratowski finite subset
import Algebra.Construct.Free.Semilattice using (𝒦)

-- Definition 20: Membership of 𝒦
import Algebra.Construct.Free.Semilattice.Relation.Unary using (_∈_)

-- Definition 21: Kuratowski finiteness
import Cardinality.Finite.Kuratowski using (𝒦ᶠ)

-- Lemma 9
import Cardinality.Finite.Kuratowski using (isProp𝒦ᶠ)

-- Lemma 10
import Cardinality.Finite.Kuratowski using (𝒦ᶠ⟨S¹⟩)

--------------------------------------------------------------------------------
-- Section 3: Relations Between Each Finiteness Definition
--------------------------------------------------------------------------------

-- Lemma 11
import Cardinality.Finite.ManifestBishop using (ℰ!⇒ℬ)

-- Lemma 12
import Cardinality.Finite.ManifestBishop using (ℬ⇒ℰ!)

-- Lemma 13
import Cardinality.Finite.ManifestEnumerable using (ℰ!⇒ℰ)

-- Lemma 14
import Cardinality.Finite.ManifestEnumerable using (ℰ⇒ℰ!)

-- Lemma 15
import Cardinality.Finite.Cardinal using (ℬ⇒𝒞)

-- Theorem 1
import Cardinality.Finite.Cardinal using (𝒞⇒ℬ)

-- Definition 22: List Permutations
import Data.List.Relation.Binary.Permutation using (_↭_)

-- Lemma 16
import Cardinality.Finite.Kuratowski using (𝒞⇔𝒦×Discrete)

--------------------------------------------------------------------------------
-- Section 4: Relations Between Each Finiteness Definition
--------------------------------------------------------------------------------

-- Lemma 17
import Cardinality.Finite.SplitEnumerable using (ℰ!⟨⊥⟩; ℰ!⟨⊤⟩; ℰ!⟨2⟩)

-- Lemma 18
import Cardinality.Finite.SplitEnumerable using (_|Σ|_)

-- Lemma 19
import Cardinality.Finite.ManifestBishop using (_|Π|_)

-- Lemma 20
import Cardinality.Finite.Cardinal using (𝒞⇒Choice)

-- Resulting closures on 𝒞:
import Cardinality.Finite.Cardinal using
  (_∥Σ∥_; _∥⊎∥_; _∥Π∥_; _∥→∥_; _∥×∥_; _∥⇔∥_; 𝒞⟨⊥⟩; 𝒞⟨⊤⟩; 𝒞⟨Bool⟩)

-- Theorem 2:
import Cardinality.Finite.Cardinal.Category using (finSetCategory)

-- Quotients are effective
import Cubical.HITs.SetQuotients.Properties using (isEquivRel→isEffective)

-- Theorem 3:
import Cardinality.Finite.Cardinal.Category using
  ( finSetHasProducts
  ; finSetHasExp
  ; finSetHasPullbacks
  ; finSetTerminal
  ; finSetInitial
  ; finSetCoeq
  ; module PullbackSurjProofs
  )

-- Same for hSets
import Categories.HSets using
  ( hSetProd
  ; hSetExp
  ; hSetHasPullbacks
  ; hSetTerminal
  ; hSetInitial
  ; hSetCoeq
  ; module PullbackSurjProofs
  )

--------------------------------------------------------------------------------
-- Section 5: Countably Infinite Types
--------------------------------------------------------------------------------

-- Definition 23: Streams
import Codata.Stream using (Stream)

-- Definition 24: Split Countability
import Cardinality.Infinite.Split using (ℰ!)

-- Definition 25: Countability
import Cardinality.Infinite.Split using (ℰ)

-- Lemma 21
import Cardinality.Infinite.Split using (ℰ⇒Discrete)

-- Theorem 4
import Cardinality.Infinite.Split using (_|Σ|_)

-- Theorem 5
import Cardinality.Infinite.Split using (|star|)

--------------------------------------------------------------------------------
-- Section 6: Search
--------------------------------------------------------------------------------

-- Definition 26: Omniscience
import Relation.Nullary.Omniscience using (Omniscient)

-- Definition 27: Exhaustibility
import Relation.Nullary.Omniscience using (Exhaustible)

import Cardinality.Finite.Kuratowski using (𝒦ᶠ⇒Exhaustible)
import Relation.Nullary.Omniscience using (Omniscient→Exhaustible)
import Cardinality.Finite.ManifestEnumerable using (ℰ⇒Omniscient)
import Cardinality.Finite.Kuratowski using (𝒦ᶠ⇒∣Omniscient∣)

import Data.Pauli using (Pauli)
import Data.Pauli using (assoc-·)
import Data.Pauli using (not-spec)
