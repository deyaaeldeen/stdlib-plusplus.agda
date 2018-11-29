open import Data.Nat

module Data.Fin.Substitution.OrVariables (T : Set) where

open import Function hiding (id; _⟨_⟩_)
open import Data.Vec as Vec hiding (_++_; [_])
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas

open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Sum as Sum using ()

pattern ground t = Sum.inj₁ t
pattern var x = Sum.inj₂ x

OrVar : ℕ → Set
OrVar = const T ∪ Fin

module App {ℓ}{T : ℕ → Set ℓ} (l : Lift T OrVar) where
  open Lift l

  _/_ : ∀ {n m} → OrVar n → Sub T n m → OrVar m
  ground t / ρ = ground t
  var x / ρ = lift $ lookup x ρ

  open Application (record { _/_ = _/_ }) using (_/✶_)
  open import Data.Star

  ground-/✶ : ∀ {m n}{s} → (ρs : Subs T m n) → (ground s) /✶ ρs ≡ ground s
  ground-/✶ ε = refl
  ground-/✶ (x ◅ ρs) = cong (Function.flip _/_ x) (ground-/✶ ρs)

termSubst : TermSubst OrVar
termSubst = record
  { var = var ;
    app = App._/_ }

open TermSubst termSubst hiding (var; subst) public

module OrVarLemmas where

  module _ {T₁ T₂ : ℕ → Set} {lift₁ : Lift T₁ OrVar} {lift₂ : Lift T₂ OrVar}{m n : ℕ}
            (ρs₁ : Subs T₁ m n)(ρs₂ : Subs T₂ m n)
            (ih : ∀ k (x : Fin (k + m)) →
              (lift₁ Lifted./✶ TermSubst.var termSubst x) ((lift₁ Lifted.↑✶ ρs₁) k)
              ≡
              (lift₂ Lifted./✶ TermSubst.var termSubst x) ((lift₂ Lifted.↑✶ ρs₂) k)) where

    /✶-↑✶ : ∀ (k : ℕ) (t : OrVar (k + m)) →
            (lift₁ Lifted./✶ t) ((lift₁ Lifted.↑✶ ρs₁) k) ≡ (lift₂ Lifted./✶ t) ((lift₂ Lifted.↑✶ ρs₂) k)
    /✶-↑✶ k (ground x) =
      trans
        (App.ground-/✶ lift₁ ((lift₁ Lifted.↑✶ ρs₁) k))
        (sym $ App.ground-/✶ lift₂ ((lift₂ Lifted.↑✶ ρs₂) k))
    /✶-↑✶ k (var y) = ih k y

  termLemmas : TermLemmas OrVar
  termLemmas = record
    { termSubst = termSubst
    ; app-var = refl
    ; /✶-↑✶ = /✶-↑✶ }

  open TermLemmas termLemmas public hiding (/✶-↑✶)
