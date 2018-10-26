open import Data.Fin.Substitution
open import Data.Nat
open import Relation.Unary

module Data.Fin.Substitution.Extra {ℓ}{T : Pred ℕ ℓ}(simple : Simple T) where

open import Function
open import Data.Fin as Fin
open import Data.Vec
open import Relation.Nullary.Decidable
open import Relation.Nullary

open Simple simple

{- useful parallel substitutions -}
wk-at : ∀ {n} → Fin (ℕ.suc n) → Sub T n (ℕ.suc n)
wk-at x = tabulate (var ∘ punchIn x)

_for_ : ∀ {v} → T v → Fin (suc v) → Fin (suc v) → T v
(t for x) y with x Fin.≟ y
... | yes eq = t
... | no ¬eq = var (punchOut ¬eq)

sub_at_ : ∀ {n} → T n → Fin (ℕ.suc n) → Sub T (ℕ.suc n) n
sub t at x = tabulate (t for x)
