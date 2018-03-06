open import Relation.Binary hiding (_⇒_)
open import Level

module Relation.Unary.Monotone {c i}(pre : Preorder i c i) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_)
open import Relation.Unary

record Monotone {ℓ}(p : Pred I ℓ) : Set (i ⊔ ℓ) where
  field wk : ∀ {i j} → i ≤ j → p i → p j

open Monotone
open Monotone ⦃...⦄ public

infixr 4 _↗_
_↗_ : ∀ {ℓ} → Pred I ℓ → Pred I ℓ → Pred I (i ⊔ ℓ)
(P ↗ Q) i = ∀ {j} → i ≤ j → P j → Q j

instance
  ↗-monotone : ∀ {ℓ}{P Q : Pred I ℓ} → Monotone (P ↗ Q)
  wk ↗-monotone ext f ext' = f (trans ext ext')
