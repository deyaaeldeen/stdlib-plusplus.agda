module Data.List.Membership.Extra {ℓ}{A : Set ℓ} where

open import Data.List
open import Data.List.Any
open import Data.List.Membership.Propositional

without : ∀ {l : List A}{x} → x ∈ l → List A
without (here  {_}{xs} _) = xs
without (there {x}{_}  p) = x ∷ without p
