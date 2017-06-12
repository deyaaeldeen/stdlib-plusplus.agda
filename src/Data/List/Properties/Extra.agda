module Data.List.Properties.Extra where

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Data.List
open import Data.Product hiding (map)
open import Data.Fin using (fromℕ≤; zero; suc)
open import Data.List.All hiding (lookup; map)
open import Data.List.Any hiding (map)
open import Data.List.At
open Membership-≡

open import Relation.Binary.List.Pointwise hiding (refl; map)
open import Relation.Binary.PropositionalEquality

∈-∷ʳ : ∀ {a}{A : Set a}(l : List A)(x : A) → x ∈ (l ∷ʳ x)
∈-∷ʳ [] x = here refl
∈-∷ʳ (x ∷ l) y = there (∈-∷ʳ l y)

infixl 10 _[_]≔_
_[_]≔_ : ∀ {a} {A : Set a} → (l : List A) → Fin (length l) → A → List A
[] [ () ]≔ x
(x ∷ xs) [ zero ]≔ x' = x' ∷ xs
(x ∷ xs) [ suc i ]≔ y = xs [ i ]≔ y

infixl 10 _[_]≔'_
_[_]≔'_ : ∀ {a} {A : Set a}{x} → (l : List A) → x ∈ l → A → List A
[] [ () ]≔' y
(x ∷ l) [ here px ]≔' y = y ∷ l
(x ∷ l) [ there px ]≔' y = x ∷ (l [ px ]≔' y)

≔'-[]= :  ∀ {a} {A : Set a}{x}{l : List A} (p : x ∈ l) → ∀ {y} → y ∈ (l [ p ]≔' y)
≔'-[]= (here px) = here refl
≔'-[]= (there p) = there (≔'-[]= p)

-- proof matters; update a particular witness of a property
_All[_]≔_ : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {i x} →
            All P xs → xs [ i ]= x → P x → All P xs
_All[_]≔_ [] ()
_All[_]≔_ {xs = .(_ ∷ _)} {zero} (px ∷ xs) refl px' = px' ∷ xs
_All[_]≔_ {xs = .(_ ∷ _)} {suc i} (px ∷ xs) q px' = px ∷ (xs All[ q ]≔ px')

all-∷ʳ : ∀ {a p} {A : Set a} {l : List A} {x} {P : A → Set p} → All P l → P x → All P (l ∷ʳ x)
all-∷ʳ [] q = q ∷ []
all-∷ʳ (px ∷ p) q = px ∷ (all-∷ʳ p q)
