module Data.List.Properties.Extra {a}{A : Set a} where

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Data.List
open import Data.Product hiding (map)
open import Data.Fin using (fromℕ≤; zero; suc)
open import Data.List.All hiding (lookup; map)
open import Data.List.Any hiding (map)
open import Data.List.Any.Membership.Propositional

open import Relation.Binary.List.Pointwise hiding (refl; map)
open import Relation.Binary.PropositionalEquality

∈-∷ʳ : ∀ (l : List A)(x : A) → x ∈ (l ∷ʳ x)
∈-∷ʳ [] x = here refl
∈-∷ʳ (x ∷ l) y = there (∈-∷ʳ l y)

infixl 10 _[_]≔_
_[_]≔_ : (l : List A) → Fin (length l) → A → List A
[] [ () ]≔ x
(x ∷ xs) [ zero ]≔ x' = x' ∷ xs
(x ∷ xs) [ suc i ]≔ y = xs [ i ]≔ y

infixl 10 _[_]≔'_
_[_]≔'_ : ∀ {x} → (l : List A) → x ∈ l → A → List A
[] [ () ]≔' y
(x ∷ l) [ here px ]≔' y = y ∷ l
(x ∷ l) [ there px ]≔' y = x ∷ (l [ px ]≔' y)

≔'-[]= :  ∀ {x}{l : List A} (p : x ∈ l) → ∀ {y} → y ∈ (l [ p ]≔' y)
≔'-[]= (here px) = here refl
≔'-[]= (there p) = there (≔'-[]= p)

drop-prefix : ∀ (l m : List A) → drop (length l) (l ++ m) ≡ m
drop-prefix [] m = refl
drop-prefix (x ∷ l) m = drop-prefix l m
