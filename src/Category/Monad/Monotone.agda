open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality

module Category.Monad.Monotone {ℓ}(pre : Preorder ℓ ℓ ℓ) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_)

open import Level
open import Relation.Unary
open import Relation.Unary.Monotone pre
open import Relation.Unary.PredicateTransformer using (Pt)

record RawMPMonad (M : Pt I ℓ) : Set (suc ℓ) where

  infixl 1 _≥=_
  field
    return : ∀ {P} → P ⊆ M P
    _≥=_   : ∀ {P Q} → M P ⊆ ((P ↗ M Q) ⇒ M Q)

  -- we get the predicate-monad bind for free
  _>>=_ : ∀ {P Q} → M P ⊆ (λ i → (P ⊆ M Q) → M Q i)
  c >>= f = c ≥= λ i≤j pj → f pj

  -- which is only useful because we also get monadic strength for free:
  open import Data.Product
  _^_ : ∀ {P Q : Pred I ℓ}⦃ m : Monotone Q ⦄ → M P ⊆ (λ i → Q i → M (P ∩ Q) i)
  c ^ qi = c ≥= λ {j} x≤j pj → return (pj , wk x≤j qi)

  open import Category.Monad.Predicate
  pmonad : RawPMonad {ℓ = ℓ} M
  pmonad = record
    { return? = return
    ; _=<?_ = λ f px → px >>= f }
