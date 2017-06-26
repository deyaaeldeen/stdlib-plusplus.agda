module Data.List.All.Properties.Extra {a}{A : Set a} where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.List.Properties.Extra
open import Data.List.At
open import Data.List.All
open import Data.List.All.Properties
open import Data.Product

drop-all : ∀ {p}{P : A → Set p}{l : List A} n → All P l → All P (drop n l)
drop-all zero px = px
drop-all (suc n) [] = []
drop-all (suc n) (px ∷ pxs) = drop-all n pxs

split-++ : ∀ {p}{P : A → Set p}(l m : List A) → All P (l ++ m) → All P l × All P m
split-++ [] m pxs = [] , pxs
split-++ (x ∷ l) m (px ∷ pxs) with split-++ l m pxs
... | lp , rp = px ∷ lp , rp

_++-all_ : ∀ {l m p}{P : A → Set p} → All P l → All P m → All P (l ++ m)
[] ++-all pm = pm
(px ∷ pl) ++-all pm = px ∷ (pl ++-all pm)

∈-all : ∀ {p}{P : A → Set p}{l : List A}{x} → x ∈ l → All P l → P x
∈-all (here refl) (px ∷ q) = px
∈-all (there p) (px ∷ q) = ∈-all p q

-- proof matters; update a particular witness of a property
_All[_]≔_ : ∀ {p}{P : A → Set p} {xs : List A} {i x} →
            All P xs → xs [ i ]= x → P x → All P xs
_All[_]≔_ [] ()
_All[_]≔_ {xs = .(_ ∷ _)} {zero} (px ∷ xs) refl px' = px' ∷ xs
_All[_]≔_ {xs = .(_ ∷ _)} {suc i} (px ∷ xs) q px' = px ∷ (xs All[ q ]≔ px')

_All[_]≔'_ : ∀ {p}{P : A → Set p} {xs : List A} {x} →
            All P xs → x ∈ xs → P x → All P xs
_All[_]≔'_ [] ()
_All[_]≔'_ {xs = .(_ ∷ _)} (px ∷ xs) (here refl) px' = px' ∷ xs
_All[_]≔'_ {xs = .(_ ∷ _)} (px ∷ xs) (there t) px' = px ∷ (xs All[ t ]≔' px')

all-∷ʳ : ∀ {p}{l : List A} {x} {P : A → Set p} → All P l → P x → All P (l ∷ʳ x)
all-∷ʳ [] q = q ∷ []
all-∷ʳ (px ∷ p) q = px ∷ (all-∷ʳ p q)
