module Data.Fin.Subset.Properties.Extra where

open import Data.Product
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties

⊥-Empty : ∀ {n} → Empty {n} ⊥
⊥-Empty (_ , x∈⊥) = ∉⊥ x∈⊥
