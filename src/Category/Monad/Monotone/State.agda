open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality
open import Level

module Category.Monad.Monotone.State {ℓ}(pre : Preorder ℓ ℓ ℓ)(H : Preorder.Carrier pre → Set ℓ) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl; trans to ≤-trans)

open import Data.Unit using (⊤; tt)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Monotone pre
open import Data.Product
open import Category.Monad
open import Category.Monad.Monotone pre
open import Category.Monad.Identity

MST : (Set ℓ → Set ℓ) → Pt I ℓ
MST M P = H ⇒ (λ i → M (∃ λ j → i ≤ j × H j × P j))

MSt : Pt I ℓ
MSt = MST Identity

record StateMonad M ⦃ Mon : RawMPMonad M ⦄ : Set (suc ℓ) where
  open RawMPMonad Mon
  field
    get : ∀ {i} → M H i
    put : H ⊆ M (λ i → Lift ⊤)

  state : (H ↗ H) ⊆ M (λ i → Lift ⊤)
  state f = do
    s , f' ← _^_ {Q = H ↗ H} get f
    let s' = f' ≤-refl s
    put s'

  puts = state

module _ {M} ⦃ Mon : RawMonad {ℓ} M ⦄ where

  private module M = RawMonad Mon

  instance
    open RawMPMonad public
    monad : RawMPMonad (MST M)
    return monad px μ = M.return (_ , ≤-refl , μ , px)
    _≥=_ monad c f  μ = c μ M.>>= λ where
      (i₁ , ext₁ , μ₁ , pv) → (f ext₁ pv μ₁) M.>>= λ where
        (i₂ , ext₂ , μ₂ , pw) → M.return (i₂ , ≤-trans ext₁ ext₂ , μ₂ , pw)

    open StateMonad
    mst-monad-ops : StateMonad (MST M)
    get (mst-monad-ops) μ = M.return (_ , ≤-refl , μ , μ)
    put (mst-monad-ops) μ' μ = M.return (_ , ≤-refl , μ' , lift tt)
