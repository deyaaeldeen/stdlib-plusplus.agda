module Data.Fin.Unification where

-- Unification using structural recursion a la McBride

open import Function

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (_+_)
open import Data.Fin.Substitution using (Simple)
open import Data.Product
open import Data.Maybe

open import Relation.Unary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module _ {ℓ}(T : Pred ℕ ℓ) where
  data Sub : ℕ → ℕ → Set ℓ where
    anil      : ∀ {n} → Sub n n
    _asnoc_/_ : ∀ {m n} → Sub m n → T m → Fin (suc m) → Sub (suc m) n

  Unifier : Pred ℕ ℓ
  Unifier = ∃ ∘ Sub

{- operations on Subs -}
module _ {ℓ}{T : Pred ℕ ℓ} where
  _⊙_ : ∀ {m n u} → Sub T m n → Sub T n u → Sub T m u
  anil ⊙ σ = σ
  (ρ asnoc t / x) ⊙ σ = (ρ ⊙ σ) asnoc t / x

record Terms {ℓ}(T : Pred ℕ ℓ) : Set ℓ where
  field
    bind   : ∀ {m n} → (Fin m → T n) → T m → T n
    check  : ∀ {n} → Fin (suc n) → T (suc n) → Maybe (T n)

module Unifiers {ℓ}{T : Pred ℕ ℓ}(tms : Terms T)(simple : Simple T) where
  open Simple simple using (var; weaken)
  open Terms tms public

  {- lifting iterated substitutions -}
  module _ where
    _↑ : ∀ {n m} → Sub T m n → Sub T (suc m) (suc n)
    anil ↑ = anil
    (ρ asnoc t / x) ↑ = (ρ ↑) asnoc (weaken t) / (suc x)

    _↑⋆_ : ∀ {n m} → Sub T m n → ∀ k → Sub T (k + m) (k + n)
    ρ ↑⋆ zero = ρ
    _↑⋆_ {n}{m} ρ (suc k) = subst₂ (Sub T) (+-suc k m) (+-suc k n) ((ρ ↑) ↑⋆ k)

  {- functional interpretation of iterated substitution -}
  module _ where
    _for_ : ∀ {v} → T v → Fin (suc v) → Fin (suc v) → T v
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
    flex-flex {zero} ()
    flex-flex {suc m} x y with x Fin.≟ y
    ... | yes eq = _ , anil
    ... | no ¬eq = _ , (anil asnoc (var (punchOut ¬eq)) / x)

    flex-rigid : ∀ {m} → Fin m → T m → Maybe (Unifier T m)
    flex-rigid {zero} () t
    flex-rigid {suc m} x t with check x t
    ... | just t' = just (_ , anil asnoc t' / x)
    ... | nothing = nothing

record Unification {ℓ}(T : Pred ℕ ℓ) : Set ℓ where
  field
    tms    : Terms T
    simple : Simple T

  open Unifiers tms simple public

  field
    unify : ∀ {n} → (l r : T n) → Maybe (Unifier T n)
