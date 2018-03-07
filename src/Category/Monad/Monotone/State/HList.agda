import Relation.Unary.Monotone as Mono

open import Data.List.Prefix
open import Data.List as List

module Category.Monad.Monotone.State.HList (T : Set)(V : T → List T → Set)⦃ wkV : ∀ {a} → Mono.Monotone ⊑-preorder (V a) ⦄ where

open import Data.List.All as All
open import Data.List.All.Properties.Extra
open import Data.List.Any
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.Properties.Extra
open import Data.Product

open import Relation.Binary using (Preorder)
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Monotone.Prefix {T = T}

private
  HeapT : Set
  HeapT = List T

  Heap : Pred HeapT _
  Heap = λ W → All (λ a → V a W) W

open Mono (⊑-preorder {A = T})
open import Category.Monad.Monotone (⊑-preorder {A = T})
open import Category.Monad.Monotone.State ⊑-preorder Heap
open import Category.Monad using (RawMonad)

module _ {M : Set → Set}⦃ Mon : RawMonad M ⦄ where
  private module M = RawMonad Mon

  store  : ∀ {a} → V a ⊆ MST M (λ W → a ∈ W)
  store {a}{i} sv μ = let ext = ∷ʳ-⊒ a i in M.return (_ , ext , (wk ext μ all-∷ʳ wk ext sv) , ∈-∷ʳ i a )

  storeₙ  : ∀ {as W} → All (λ a → V a W) as → MST M (λ W' → All (λ a → a ∈ W') as) W
  storeₙ [] = return []
  storeₙ (v ∷ vs) = do
    (r , vs) ← store v ^ vs
    (rs , r) ← storeₙ vs ^ r
    return (r ∷ rs)

  open import Data.Unit using (⊤; tt)
  modify   : ∀ {a} → _∈_ a ⊆ V a ⇒ MST M (λ W' → ⊤)
  modify ptr v μ = M.return (_ , ⊑-refl , μ All[ ptr ]≔' v , tt)

  deref : ∀ {a} → _∈_ a ⊆ MST M (V a)
  deref ptr μ = M.return (_ , ⊑-refl , μ , ∈-all ptr μ)
