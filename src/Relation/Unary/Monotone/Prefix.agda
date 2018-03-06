module Relation.Unary.Monotone.Prefix {ℓ}{T : Set ℓ} where

open import Data.List.Prefix
open import Data.List as List
open import Data.List.Any.Membership.Propositional
open import Data.List.All as All

open import Relation.Unary.Monotone (⊑-preorder {A = T})

instance
  open Monotone

  any-monotone : ∀ {x : T} → Monotone (λ xs → x ∈ xs)
  wk any-monotone ext l = ∈-⊒ l ext

  all-monotone : ∀ {B : Set}{xs : List B}{C : B → List T → Set}
                  ⦃ wₐ : ∀ x → Monotone (C x) ⦄ →
                  Monotone (λ ys → All (λ x → C x ys) xs)
  wk (all-monotone ⦃ wₐ ⦄) ext v = All.map (λ {a} y → wk (wₐ a) ext y) v

  list-monotone : ∀ {B : List T → Set}⦃ wb : Monotone B ⦄ → Monotone (λ W → List (B W))
  wk (list-monotone ⦃ wₐ ⦄) ext v = List.map (wk wₐ ext) v
