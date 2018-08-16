module Data.Fin.Unification where

-- Unification using structural recursion a la McBride

open import Function

open import Data.Nat hiding (_⊔_)
open import Data.Fin as Fin
open import Data.Product
open import Data.Maybe

open import Relation.Unary
open import Relation.Nullary

module _ {ℓ}(T : Pred ℕ ℓ) where

  data Sub : ℕ → ℕ → Set ℓ where
    anil      : ∀ {n} → Sub n n
    _asnoc_/_ : ∀ {m n} → Sub m n → T m → Fin (ℕ.suc m) → Sub (ℕ.suc m) n

  Unifier : Pred ℕ ℓ
  Unifier = ∃ ∘ Sub

  _⊙_ : ∀ {m n u} → Sub m n → Sub n u → Sub m u
  anil ⊙ σ = σ
  (ρ asnoc t / x) ⊙ σ = (ρ ⊙ σ) asnoc t / x

record Terms {ℓ}(T : Pred ℕ ℓ) : Set ℓ where
  field
    var   : ∀ {n}   → Fin n → T n
    bind  : ∀ {m n} → (Fin m → T n) → T m → T n
    check : ∀ {n} → Fin (ℕ.suc n) → T (ℕ.suc n) → Maybe (T n)

module Unification {ℓ}{T : Pred ℕ ℓ}(terms : Terms T)where
  open Terms terms

  {- functional interpretation of iterated substitution -}
  module _ where
    _for_ : ∀ {v} → T v → Fin (ℕ.suc v) → Fin (ℕ.suc v) → T v
    (t for x) y with x Fin.≟ y
    ... | yes eq = t
    ... | no ¬eq = var (punchOut ¬eq)

    asub : ∀ {m n} → Sub T m n → Fin m → T n
    asub anil = var
    asub (ρ asnoc t / x) = bind (asub ρ) ∘ (t for x)

    _/_ : ∀ {m n} → T m → Sub T m n → T n
    t / ρ = bind (asub ρ) t

  {- unification -}
  module _ where

    flex-flex : ∀ {m} → (x y : Fin m) → Unifier T m
    flex-flex {ℕ.zero} ()
    flex-flex {ℕ.suc m} x y with x Fin.≟ y
    ... | yes eq = _ , anil
    ... | no ¬eq = _ , (anil asnoc (var (punchOut ¬eq)) / x)

    flex-rigid : ∀ {m} → Fin m → T m → Maybe (Unifier T m)
    flex-rigid {zero} () t
    flex-rigid {ℕ.suc m} x t with check x t
    ... | just t' = just (_ , anil asnoc t' / x)
    ... | nothing = nothing
