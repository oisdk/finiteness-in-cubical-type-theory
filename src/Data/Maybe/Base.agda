{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Base where

open import Level

data Maybe (A : Type a) : Type a where
  nothing : Maybe A
  just : A → Maybe A

maybe : {B : Maybe A → Type b} → B nothing → ((x : A) → B (just x)) → (x : Maybe A) → B x
maybe b f nothing = b
maybe b f (just x) = f x
