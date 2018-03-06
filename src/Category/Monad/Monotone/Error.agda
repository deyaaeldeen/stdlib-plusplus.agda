open import Relation.Binary hiding (_⇒_)

module Category.Monad.Monotone.Error {i}(Exc : Set i)(pre : Preorder i i i) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl)

open import Function
open import Level hiding (lift)
open import Data.Sum

open import Relation.Unary
open import Relation.Unary.Monotone pre
open import Relation.Unary.PredicateTransformer

open import Category.Monad.Monotone pre
open import Category.Monad.Monotone.Identity pre

pattern left x = inj₁ x
pattern right x = inj₂ x

ErrorT : Pt I i → Pt I i
ErrorT M P = M (λ i → Exc ⊎ P i)

Error = ErrorT Identity

record ErrorMonad (M : Pt I i) : Set (suc i) where
  field
    throw : ∀ {P i} → Exc → M P i
    catch : ∀ {P}   → M P ⊆ ((const Exc ↗ M P) ⇒ M P)

module _ {M}⦃ Mon : RawMPMonad M ⦄ where
  private module M = RawMPMonad Mon

  instance
    open RawMPMonad
    error-monad : RawMPMonad (ErrorT M)
    return error-monad px = M.return (right px)
    _≥=_ error-monad {P}{Q} px f = px M.≥= λ where
        _ (left e)  → M.return (left e)
        w (right x) → f w x

    open ErrorMonad
    error-monad-ops : ErrorMonad (ErrorT M)
    throw error-monad-ops e = M.return (left e)
    catch error-monad-ops c f = c M.≥= λ where
      w (left e)  → f w e
      w (right x) → M.return (right x)

  lift-error : ∀ {P} → M P ⊆ ErrorT M P
  lift-error x = x M.>>= (λ z → M.return (right z))
