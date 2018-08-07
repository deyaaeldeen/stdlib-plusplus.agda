module Data.Sum.Extra {a}{A B : Set a} where

open import Relation.Nullary

open import Data.Unit
open import Data.Empty
open import Data.Sum

IsInj₁ : A ⊎ B → Set
IsInj₁ (inj₁ _) = ⊤
IsInj₁ (inj₂ _) = ⊥

IsInj₂ : A ⊎ B → Set
IsInj₂ (inj₁ _) = ⊥
IsInj₂ (inj₂ _) = ⊤

¬inj₁ : ∀ (p : A ⊎ B) → ¬ (IsInj₁ p) → IsInj₂ p
¬inj₁ (inj₁ x) ¬inj₁ = ¬inj₁ tt
¬inj₁ (inj₂ y) ¬inj₁ = tt

¬inj₂ : ∀ (p : A ⊎ B) → ¬ (IsInj₂ p) → IsInj₁ p
¬inj₂ (inj₁ y) ¬inj₁ = tt
¬inj₂ (inj₂ x) ¬inj₂ = ¬inj₂ tt

is-inj₁ : ∀ (p : A ⊎ B) → Dec (IsInj₁ p)
is-inj₁ (inj₁ x) = yes tt
is-inj₁ (inj₂ y) = no (λ z → z)

is-inj₂ : ∀ (p : A ⊎ B) → Dec (IsInj₂ p)
is-inj₂ (inj₁ x) = no (λ z → z)
is-inj₂ (inj₂ y) = yes tt
