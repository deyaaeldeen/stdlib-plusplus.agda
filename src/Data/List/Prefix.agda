module Data.List.Prefix where

open import Data.Nat
open import Data.List.At
open import Data.List.Any hiding (map)
open Membership-≡
open import Relation.Binary.Core using (REL; Reflexive; Transitive)
open import Relation.Binary.List.Pointwise hiding (refl; map)
open import Data.List

-- prefix predicate for lists
infix 4 _⊑_
data _⊑_ {a} {A : Set a} : List A → List A → Set where
  [] : ∀ {ys} → [] ⊑ ys
  _∷_ : ∀ x {xs ys} → xs ⊑ ys → x ∷ xs ⊑ x ∷ ys

⊑-refl : ∀ {a} {A : Set a} → Reflexive (_⊑_ {A = A})
⊑-refl {x = []} = []
⊑-refl {x = x ∷ xs} = x ∷ ⊑-refl

⊑-trans : ∀ {a} {A : Set a} → Transitive (_⊑_ {A = A})
⊑-trans [] _ = []
⊑-trans (x ∷ p) (.x ∷ q) = x ∷ ⊑-trans p q

-- list extensions; reverse prefix relation
infix 4 _⊒_
_⊒_ : ∀ {a} {A : Set a} → List A → List A → Set
xs ⊒ ys = ys ⊑ xs

-- appending to a list gives a list extension;
-- or, appending to a list makes the original a prefix
∷ʳ-⊒ : ∀ {a} {A : Set a} (x : A) xs → xs ∷ʳ x ⊒ xs
∷ʳ-⊒ x [] = []
∷ʳ-⊒ x (x₁ ∷ Σ₁) = x₁ ∷ (∷ʳ-⊒ x Σ₁)

-- indexes into a prefix point to the same element in extensions
xs⊒ys[i] : ∀ {a} {A : Set a} {xs : List A} {ys : List A} {i y} →
           xs [ i ]= y → (p : ys ⊒ xs) → ys [ i ]= y
xs⊒ys[i] () []
xs⊒ys[i] {i = zero} p (x ∷ a) = p
xs⊒ys[i] {i = suc i} p (x ∷ a) = xs⊒ys[i] p a

-- prefix is preserved by map
⊑-map : ∀ {a b} {A : Set a} {B : Set b} {xs ys : List A} {f : A → B} →
        xs ⊑ ys → map f xs ⊑ map f ys
⊑-map [] = []
⊑-map {f = f} (x ∷ p) = f x ∷ (⊑-map p)

-- all elemens in a list, also exist in it's extensions
∈-⊒ : ∀ {a}{A : Set a}{xs : List A}{x} → x ∈ xs → ∀ {ys} → ys ⊒ xs → x ∈ ys
∈-⊒ () []
∈-⊒ (here px) (x ∷ q) = here px
∈-⊒ (there p) (x ∷ q) = there (∈-⊒ p q)
