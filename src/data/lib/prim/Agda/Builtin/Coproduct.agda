{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erasure #-}

module Agda.Builtin.Coproduct where

open import Agda.Primitive

data _⊎_ {@0 a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

{-# BUILTIN COPRODUCT _⊎_ #-}
