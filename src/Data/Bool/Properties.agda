{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Bool.Properties where

open import Prelude
open import Data.Bool
open import Data.Unit.Properties

T? : ∀ x → Dec (T x)
T? x .does = x
T? false .why = ofⁿ id
T? true  .why = ofʸ tt

isPropT : ∀ x → isProp (T x)
isPropT false = isProp⊥
isPropT true  = isProp⊤
