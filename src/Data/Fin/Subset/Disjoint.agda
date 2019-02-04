module Data.Fin.Subset.Disjoint where

open import Data.Nat
open import Data.Vec
open import Data.Fin
open import Data.List as List hiding (zipWith)
open import Data.Fin.Subset
open import Data.Product

open import Relation.Binary.PropositionalEquality

-- disjointness and relational specifiation of disjoint union
module _ {n} where

  _◆_ : Subset n → Subset n → Set
  l ◆ r = Empty (l ∩ r)

  _⊎_cover_ : (xs ys zs : Subset n) → Set
  xs ⊎ ys cover zs = xs ◆ ys × xs ∪ ys ≡ zs

-- picking from support
module _ {n} where
  _⊇⟨_⟩_ : Subset n → (l : ℕ) → Vec (Fin n) l → Set
  xs ⊇⟨ l ⟩ ys = All (λ y → y ∈ xs) ys
    where open import Data.Vec.All
