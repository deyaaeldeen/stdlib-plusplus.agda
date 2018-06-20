module Data.Fin.Subset.Disjoint.Properties where

open import Data.Nat
open import Data.Vec hiding (_++_)
open import Data.Fin
open import Data.Fin.Subset.Properties
open import Data.List as List hiding (zipWith)
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import Data.Fin.Subset
open import Data.Fin.Subset.Disjoint

-- properties of disjoint subsets x ◆ y
module _ where

  ∪ᵣ-◆ : ∀ {n}{x y z : Subset n} → (x ∪ y) ◆ z → y ◆ z
  ∪ᵣ-◆ p (i , i∈y∩z) =
    let
      (i∈y , i∈z) = x∈p∩q⁻ _ _ i∈y∩z
      i∈x∪y = q⊆p∪q _ _ i∈y
    in p (i , x∈p∩q⁺ (i∈x∪y , i∈z))

  ∪ₗ-◆ : ∀ {n}{x y z : Subset n} → (x ∪ y) ◆ z → x ◆ z
  ∪ₗ-◆ {x = x}{y} rewrite ∪-comm x y = ∪ᵣ-◆

  ◆-∪ : ∀ {n}{x y z : Subset n} → x ◆ y → x ◆ z → x ◆ (y ∪ z)
  ◆-∪ x◆y x◆z (i , i∈x∩y∪z) with x∈p∪q⁻ _ _ (proj₂ (x∈p∩q⁻ _ _ i∈x∩y∪z))
  ... | inj₁ i∈y = x◆y (i , (x∈p∩q⁺ (proj₁ (x∈p∩q⁻ _ _ i∈x∩y∪z) , i∈y)))
  ... | inj₂ i∈z = x◆z (i , (x∈p∩q⁺ (proj₁ (x∈p∩q⁻ _ _ i∈x∩y∪z) , i∈z)))

-- properties of disjoint unions z of xs (xs ⨄ z)
module _ where

  -- append for disjoint disjoint-unions of subsets
  ++-⨄ : ∀ {n}{xs ys}{x y : Subset n} → xs ⨄ x → ys ⨄ y → (x ◆ y) → (xs ++ ys) ⨄ (x ∪ y)
  ++-⨄ {x = x}{y} [] q d rewrite ∪-identityˡ y = q
  ++-⨄ {y = y} (_∷_ {x = x}{z} x◆z xs⊎y) ys⊎z x∪z⊎y rewrite ∪-assoc x z y =
    (◆-∪ x◆z (∪ₗ-◆ x∪z⊎y)) ∷ (++-⨄ xs⊎y ys⊎z (∪ᵣ-◆ x∪z⊎y))

  ⨄-trans : ∀ {n}{xs ys}{x y : Subset n} → xs ⨄ x → (x ∷ ys) ⨄ y → (xs ++ ys) ⨄ (x ∪ y)
  ⨄-trans {x = x}{y} xs▰x (_∷_ {y = z} x◆y ys▰y) rewrite sym (∪-assoc x x z) =
    subst (λ x → _ ⨄ (x ∪ z)) (sym (∪-idem x)) (++-⨄ xs▰x ys▰y x◆y)
