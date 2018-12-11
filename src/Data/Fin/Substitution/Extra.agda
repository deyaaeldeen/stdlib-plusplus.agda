open import Data.Fin.Substitution
open import Data.Nat
open import Relation.Unary

module Data.Fin.Substitution.Extra {ℓ}{T : Pred ℕ ℓ}(simple : Simple T) where

open import Function
open import Data.Fin as Fin
open import Data.Vec
open import Relation.Nullary.Decidable
open import Relation.Nullary

open Simple simple
