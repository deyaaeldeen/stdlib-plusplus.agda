open import Data.Nat
open import Data.Fin.Substitution.Lemmas

module Data.Fin.Substitution.OrVariables.Nested (T₁ T₂ : ℕ → Set)(app : AppLemmas T₁ T₂) where

open import Function hiding (id; _⟨_⟩_)
open import Data.Vec as Vec hiding (_∈_; _++_; [_])
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution
open import Data.Sum renaming (inj₁ to ground; inj₂ to var)

open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Fin.Substitution.OrVariables using (OrVar)

OrVar′ : (n m : ℕ) → Set
OrVar′ n m = OrVar (T₁ m) n

open AppLemmas app using (id; application; lemmas₄) renaming (_/_ to _T/_; /-⊙ to T/-⊙)
open Lemmas₄ lemmas₄ using (_⊙_)

module _ {n} where

  private
    infixl 8 _/_
    _/_ : ∀ {m m'} → OrVar′ n m → Sub T₂ m m' → OrVar′ n m'
    var    x / ρ = var x
    ground t / ρ = ground (t T/ ρ)

    id-vanishes : ∀ {m}(t : OrVar′ n m) → t / id ≡ t
    id-vanishes (var x)    = refl
    id-vanishes (ground t) = cong ground (AppLemmas.id-vanishes app t)

    /-⊙ : ∀ {m m' m''}{ρ₁ : Sub T₂ m m'}{ρ₂ : Sub T₂ m' m''}
        (t : OrVar′ n m) → t / (ρ₁ ⊙ ρ₂) ≡ (t / ρ₁ / ρ₂)
    /-⊙ (var x) = refl
    /-⊙ (ground t) = cong ground (T/-⊙ t) -- (AppLemmas./-⊙ app t)

  lemmas : AppLemmas (OrVar′ n) T₂
  lemmas = record
    { application = record { _/_ = _/_ }
    ; lemmas₄ = lemmas₄
    ; id-vanishes = id-vanishes
    ; /-⊙ = /-⊙ }

  module OrVarLemmas = AppLemmas lemmas
