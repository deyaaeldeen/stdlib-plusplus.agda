open import Data.Nat
open import Data.Fin.Substitution.Lemmas

module Data.Fin.Substitution.Unification.Properties {T₁ : ℕ → Set} (lemmas : TermLemmas T₁) where

open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Fin.Substitution using (Sub)

open TermLemmas lemmas
open import Data.Fin.Substitution.Unification application

{- Some lemmas about unifiers -}
module _ where

  ≈≈-refl : ∀ {n} {t₁ : T₁ n} → t₁ ≈≈ t₁
  ≈≈-refl {t₁ = t₁} = unify id refl

  /-≈≈ : ∀ {n m} {t₁ t₂ : T₁ n} (ρ : Sub T₁ n m) → (t₁ / ρ) ≈≈ (t₂ / ρ) → t₁ ≈≈ t₂
  /-≈≈ ρ (unify φ eq) = unify (ρ ⊙ φ) (subst₂ _≡_ (sym (/-⊙ _)) (sym (/-⊙ _)) eq)

  /-≈/≈ : ∀ {n m} {t₁ t₂ : T₁ n} (ρ : Sub T₁ n m) → t₁ ≈/≈ t₂ → (t₁ / ρ) ≈/≈ (t₂ / ρ)
  /-≈/≈ ρ ¬u eq = ¬u (/-≈≈ ρ eq)
