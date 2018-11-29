module Data.List.Folds {a}{A : Set a} where

open import Function
open import Data.List
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.List.Relation.Subset.Propositional

open import Relation.Binary.PropositionalEquality

foldrWithin : ∀ {b}{B : Set b}(xs : List A) → (∀ {x} → x ∈ xs → B → B) → B → B
foldrWithin {b}{B} xs f z = foldrWithin′ f z xs id
  where
    foldrWithin′ : {xs : List A} → (∀ {x} → x ∈ xs → B → B) → B → (ys : List A) → ys ⊆ xs → B
    foldrWithin′ f z [] inj = z
    foldrWithin′ f z (x ∷ ys) inj = f (inj (here refl)) (foldrWithin′ f z ys (inj ∘ there))

