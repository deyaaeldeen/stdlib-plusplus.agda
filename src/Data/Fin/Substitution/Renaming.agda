module Data.Fin.Substitution.Renaming where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Substitution

open import Relation.Unary

{- just renamings; helps inference if using instance resolution -}
record Renaming {ℓ} (T : Pred ℕ ℓ) : Set ℓ where
  
  Ren : ℕ → ℕ → Set
  Ren = Sub Fin
  
  field
    rename : ∀ {n m} → Ren n m → T n → T m
 
app-ren : ∀ {ℓ₁} {T₁ : Pred ℕ ℓ₁} →
          Application T₁ Fin →
          Renaming T₁
app-ren App = record { rename = λ ρ t → Application._/_ App t ρ }
