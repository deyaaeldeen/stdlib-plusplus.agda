module Data.Fin.Unification.Lemmas where

open import Function

open import Level renaming (zero to 0ℓ)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (_+_; _≤_)
open import Data.Fin.Unification
open import Data.Fin.Substitution as Par using (Simple; TermSubst)
open import Data.Fin.Substitution.Lemmas as ParLem using (TermLemmas)
open import Data.Fin.Substitution.Lemmas.Extra
open import Data.Fin.Properties
open import Data.Product
open import Data.Vec as Vec
open import Data.Vec.Properties
open import Data.Maybe
open import Data.Empty
open import Data.Nat

open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module Lemmas₀ {ℓ} {T : Pred ℕ ℓ} where

  open import Data.Nat.Properties as ℕP

  mono : ∀ {n m} → Sub T n m → m ≤ n
  mono anil            = ℕP.≤-refl
  mono (p asnoc _ / _) = ℕP.≤-trans (mono p) (n≤1+n _)

record Lemmas₁ {ℓ T}(tms : OnTerms {ℓ} T)(simple : Par.Simple T) : Set ℓ where
  open Simple simple using (var; _for_)
  open Unifiers tms simple
  open ForLemmas simple

  field
    /-var : ∀ {n m}(x : Fin n){ρ : Fin n → T m} → bind ρ (var x) ≡ ρ x
    /-anil-vanishes : ∀ {n}{t : T n} → t / anil ≡ t
    /-⊙ : ∀ {n m l} t (ρ₁ : Sub T n m)(ρ₂ : Sub T m l) → t / ρ₁ / ρ₂ ≡ t / ρ₁ ⊙ ρ₂

  open ≡-Reasoning

  {- certain asnoc's disappear on punchIn -}
  asnoc-punchIn : ∀ {v w}(ρ : Sub T v w) x y t → asub (ρ asnoc t / x) (punchIn x y) ≡ asub ρ y
  asnoc-punchIn ρ x y t =
    begin asub (ρ asnoc t / x) (punchIn x y)
    ≡⟨⟩ bind (asub ρ) ((t for x) (punchIn x y))
    ≡⟨ cong (bind (asub ρ)) (for-punchIn x y) ⟩ bind (asub ρ) (var y)
    ≡⟨ /-var y ⟩ asub ρ y ∎

record Lemmas₂ {T}(tms : OnTerms T)(lms : TermLemmas T) : Set₁ where
  open TermLemmas lms using (simple; termSubst; ⊙-assoc; id-⊙) renaming (/-⊙ to //-⊙; var-/ to var-//)
  open Simple simple using (var; sub_at_; _for_; wk-at)
  open Unifiers tms simple
  open ForLemmas simple
  open AdditionalLemmas lms
  open TermSubst termSubst using () renaming (_⊙_ to _par-⊙_; _/_ to _//_; id to par-id)

  _[↦_] : ∀ {n m} → T n → Sub T n m → T m
  _[↦_] = λ t ρ → t // (par ρ)

  field
    /-par : ∀ {n m} (ρ : Sub T n m) t → (t / ρ) ≡ t [↦ ρ ]

  {- lemma about looking up in a converted iterated substitution -}
  lookup-par : ∀ {n m} x (ρ : Sub T n m) → lookup x (par ρ) ≡ asub ρ x
  lookup-par x ρ = lookup∘tabulate (asub ρ) x

  var-/-par : ∀ {n m} x (ρ : Sub T n m) → (var x) [↦ ρ ] ≡ asub ρ x
  var-/-par x ρ = begin
    var x // (par ρ)
    ≡⟨ var-// ⟩ lookup x (par ρ)
    ≡⟨ lookup-par x ρ ⟩ asub ρ x ∎

  var-asnoc-step : ∀ {n m} x t (ρ : Sub T n m) → (var x) [↦ (ρ asnoc t / x) ] ≡ t [↦ ρ ]
  var-asnoc-step x t ρ = begin
    var x // (par (ρ asnoc t / x))
    ≡⟨ var-/-par x (ρ asnoc t / x) ⟩ asub (ρ asnoc t / x) x
    ≡⟨ cong (bind (asub ρ)) (t-for-x x) ⟩ bind (asub ρ) t
    ≡⟨ /-par ρ t ⟩ t // par ρ ∎

  tabulate-⊙ : ∀ {n m x}{f : Fin x → T n}(ρ : Par.Sub T n m) → tabulate f par-⊙ ρ ≡ tabulate ((_// ρ) ∘ f)
  tabulate-⊙ {f = f} ρ = sym (tabulate-∘ (_// ρ) f)

  par-asnoc-step : ∀ {v w} t x (ρ : Sub T v w) → par (ρ asnoc t / x) ≡ (sub t at x) par-⊙ (par ρ)
  par-asnoc-step t x ρ = begin
    par (ρ asnoc t / x)                            ≡⟨ refl ⟩
    tabulate (bind (asub ρ) ∘ (t for x))           ≡⟨ tabulate-cong ((/-par ρ) ∘ (t for x)) ⟩
    tabulate ((_// (par ρ)) ∘ (t for x))           ≡⟨ sym (tabulate-⊙ {f = t for x} (tabulate (asub ρ))) ⟩
    (tabulate (t for x)) par-⊙ (tabulate (asub ρ)) ≡⟨ refl ⟩
    (sub t at x) par-⊙ (par ρ) ∎

  ⊙-par : ∀ {n m l} (ρ : Sub T n m)(φ : Sub T m l) → par (ρ ⊙ φ) ≡ par ρ par-⊙ (par φ)
  ⊙-par anil φ = trans (sym id-⊙) (cong (_par-⊙ (par φ)) (sym tabulate-var≡id))
  ⊙-par (ρ asnoc t / x) φ = begin
    par ((ρ ⊙ φ) asnoc t / x)              ≡⟨ par-asnoc-step t x (ρ ⊙ φ) ⟩
    (sub t at x) par-⊙ par (ρ ⊙ φ)         ≡⟨ cong ((sub t at x) par-⊙_) (⊙-par ρ φ) ⟩
    (sub t at x) par-⊙ (par ρ par-⊙ par φ) ≡⟨ ⊙-assoc ⟩
    (sub t at x) par-⊙ par ρ par-⊙ par φ   ≡⟨ cong (_par-⊙ par φ) (sym (par-asnoc-step t x ρ)) ⟩
    par (ρ asnoc t / x) par-⊙ par φ ∎

  -- Under specific conditions (sub t at x) ⊙ (wk-at x) vanishes.
  -- This lemma is generalized over φ because
  -- the then necessary equality (t // wk-at x ≡ var x) is stronger
  -- than (t // wk-at x // φ) ≡ lookup x φ
  sub-at-wk-at : ∀ {n m} x (t : T n) (φ : Par.Sub T _ m) →
                 (t // wk-at x // φ ≡ lookup x φ) →
                 (sub t at x) par-⊙ (wk-at x) par-⊙ φ ≡ φ
  sub-at-wk-at x t φ eq = begin
      (sub t at x) par-⊙ (wk-at x) par-⊙ φ
    ≡⟨ sym ⊙-assoc ⟩
      tabulate (t for x) par-⊙ ((wk-at x) par-⊙ φ)
    ≡⟨ tabulate-⊙ {f = t for x} ((wk-at x) par-⊙ φ) ⟩
      tabulate (λ i → ((t for x) i) // (wk-at x par-⊙ φ))
    ≡⟨ tabulate-cong lem ⟩
      tabulate (λ i → lookup i φ)
    ≡⟨ tabulate∘lookup φ ⟩
      φ ∎
    where
      lem : ∀ i → ((t for x) i) // (wk-at x par-⊙ φ) ≡ lookup i φ
      lem i with x Fin.≟ i
      ... | yes refl = trans (//-⊙ t) eq
      ... | no  x≢i = begin
          (var (punchOut x≢i)) // (tabulate (var ∘ punchIn x) par-⊙ φ)
        ≡⟨ //-⊙ _ ⟩
          (var (punchOut x≢i)) // tabulate (var ∘ punchIn x) // φ
        ≡⟨ cong (_// φ) var-// ⟩
          lookup (punchOut x≢i) (tabulate (var ∘ punchIn x)) // φ
        ≡⟨ cong (_// φ) (lookup∘tabulate (var ∘ punchIn x) (punchOut x≢i)) ⟩
          (var ∘ punchIn x) (punchOut x≢i) // φ
        ≡⟨ cong (λ i → var i // φ) (punchIn-punchOut x≢i) ⟩
          var i // φ
        ≡⟨ var-// ⟩
          lookup i φ ∎

  {- wk-at x ⊙ sub t at x always vanishes -}
  wk-at-sub-at : ∀ {n} x (t : T n) → (wk-at x) par-⊙ (sub t at x) ≡ par-id
  wk-at-sub-at x t = begin
    (wk-at x) par-⊙ (sub t at x)                                 ≡⟨ tabulate-⊙ (sub t at x) ⟩
    tabulate ((λ y → var (punchIn x y) // (sub t at x)))         ≡⟨ tabulate-cong (λ y → var-//) ⟩
    tabulate ((λ y → lookup (punchIn x y) (tabulate (t for x)))) ≡⟨ tabulate-cong (λ y → lookup∘tabulate (t for x) _) ⟩
    tabulate ((t for x) ∘ (punchIn x))                           ≡⟨ tabulate-cong (for-punchIn x) ⟩
    tabulate var                                                 ≡⟨ tabulate-var≡id ⟩
    par-id ∎

  var-wk-at : ∀ {n}{x : Fin (ℕ.suc n)} y → (var y) // wk-at x ≡ var (punchIn x y)
  var-wk-at y = trans var-// (lookup∘tabulate (var ∘ punchIn _) y)

  /-≡ʳ : ∀ {n m} t₁ t₂ (φ : Sub T n m) → t₁ / φ ≡ t₂ / φ → t₁ // par φ ≡ t₂ // par φ
  /-≡ʳ t₁ t₂ φ = subst₂ _≡_ (/-par φ t₁) (/-par φ t₂)

  /-≡ˡ : ∀ {n m} t₁ t₂ (φ : Sub T n m) → t₁ // par φ ≡ t₂ // par φ → t₁ / φ ≡ t₂ / φ
  /-≡ˡ t₁ t₂ φ = subst₂ _≡_ (sym $ /-par φ t₁) (sym $ /-par φ t₂)

record Lemmas₃ {T}(tms : OnTerms T) : Set₁ where
  {- parallel substitution + lemmas -}
  field
    lms : TermLemmas T

  open TermLemmas lms using (simple; termSubst; var-/; ⊙-assoc; id-⊙) renaming (/-⊙ to //-⊙)
  open Simple simple using (var; _for_; wk-at)
  open Unifiers tms simple
  open AdditionalLemmas lms
  module TmPar = TermSubst termSubst
  open TmPar using () renaming (_⊙_ to _par-⊙_; _/_ to _//_)

  {- iterated substitution + lemmas -}
  field
    super₁    : Lemmas₁ tms simple
    super₂    : Lemmas₂ tms lms

  open Lemmas₁ super₁ public
  open Lemmas₂ super₂ public

  ⊙-punchIn⋆ : ∀ {n m l} x (ρ : Sub T n m)(φ : Sub T m l) → (asub (ρ ⊙ φ)) (punchIn⋆ ρ x) ≡ (asub φ x)
  ⊙-punchIn⋆ x anil φ = refl
  ⊙-punchIn⋆ x (ρ asnoc t / y) φ = begin
      asub ((ρ ⊙ φ) asnoc t / y) (punchIn⋆ (ρ asnoc t / y) x)
    ≡⟨⟩
      asub ((ρ ⊙ φ) asnoc t / y) (punchIn y (punchIn⋆ ρ x))
    ≡⟨ asnoc-punchIn (ρ ⊙ φ) y _ t ⟩
      asub (ρ ⊙ φ) (punchIn⋆ ρ x)
    ≡⟨ ⊙-punchIn⋆ x ρ φ ⟩
      asub φ x ∎

  {- asnoc-punchin also disappears in the par version -}
  wk-at-vanishes : ∀ {v w}(ρ : Sub T v w) x t → wk-at x par-⊙ par (ρ asnoc t / x) ≡ par ρ
  wk-at-vanishes ρ x t = begin
    wk-at x par-⊙ par (ρ asnoc t / x)                        ≡⟨ tabulate-⊙ (par (ρ asnoc t / x)) ⟩
    tabulate ((_// (par (ρ asnoc t / x))) ∘ var ∘ punchIn x) ≡⟨ tabulate-cong (λ y → var-/-par (punchIn x y) (ρ asnoc t / x)) ⟩
    tabulate (asub (ρ asnoc t / x) ∘ (punchIn x))            ≡⟨ tabulate-cong (λ y → asnoc-punchIn ρ x y t) ⟩
    par ρ ∎

  {- one can push through `wk-at x` on punchIn⋆ to an instance of `punchIn x` -}
  rev-wk-⊙-wk-at : ∀ {n m}(φ : Sub T m n){x} →
                   tabulate (var ∘ punchIn⋆ φ) par-⊙ wk-at x ≡
                   tabulate (var ∘ punchIn x ∘ punchIn⋆ φ)
  rev-wk-⊙-wk-at φ {x} =
    begin
      tabulate (var ∘ (punchIn⋆ φ)) par-⊙ (wk-at x)
    ≡⟨ tabulate-⊙ (wk-at x) ⟩
      tabulate ((_// (wk-at x)) ∘ var ∘ (punchIn⋆ φ))
    ≡⟨ tabulate-cong (var-wk-at ∘ (punchIn⋆ φ)) ⟩
      tabulate (var ∘ (Fin.punchIn x) ∘ (punchIn⋆ φ)) ∎
