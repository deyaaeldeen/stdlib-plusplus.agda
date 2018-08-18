module Data.Fin.Unification.Lemmas where

open import Function

open import Level renaming (zero to 0ℓ)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Fin.Unification
open import Data.Fin.Substitution as Par using (Simple; TermSubst)
open import Data.Fin.Substitution.Lemmas as ParLem using (TermLemmas)
open import Data.Product
open import Data.Vec as Vec
open import Data.Vec.Properties
open import Data.Maybe
open import Data.Empty

open import Relation.Unary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Lemmas₀ {ℓ T}(tms : Terms {ℓ} T)(simple : Par.Simple T) : Set ℓ where
  open Simple simple
  open Unifiers tms simple

  field
    bind-var : ∀ {n m}(x : Fin n){ρ : Fin n → T m} → bind ρ (var x) ≡ ρ x

  open ≡-Reasoning

  {- substituting for a punched in' variable dissappears -}
  for-punchIn : ∀ {v}{t : T v} x y → (t for x) (punchIn x y) ≡ var y
  for-punchIn x y with x Fin.≟ (punchIn x y)
  ... | yes eq = ⊥-elim (punchInᵢ≢i _ _ (sym eq))
  ... | no ¬eq = cong var (trans (punchOut-cong x refl) (punchOut-punchIn x))

  {- certain asnoc's disappear on punchIn -}
  asnoc-punchIn : ∀ {v w}(ρ : Sub T v w) x y t → asub (ρ asnoc t / x) (punchIn x y) ≡ asub ρ y
  asnoc-punchIn ρ x y t =
    begin asub (ρ asnoc t / x) (punchIn x y)
    ≡⟨⟩ bind (asub ρ) ((t for x) (punchIn x y))
    ≡⟨ cong (bind (asub ρ)) (for-punchIn x y) ⟩ bind (asub ρ) (var y)
    ≡⟨ bind-var y ⟩ asub ρ y ∎

  t-for-x : ∀ {v}{t : T v} x → (t for x) x ≡ t
  t-for-x x with x Fin.≟ x
  ... | yes eq = refl
  ... | no ¬eq = ⊥-elim (¬eq refl)

{- Lemmas relating iterated and parallel substitution -}
record Lemmas₁ {T}(tms : Terms T) : Set₁ where
  {- parallel substitution + lemmas -}
  field
    lms : TermLemmas T

  open TermLemmas lms using (simple; termSubst; var-/; /-⊙)
  open Simple simple
  module TmPar = TermSubst termSubst
  open TmPar using () renaming (_⊙_ to _par-⊙_; _/_ to _par-/_)

  {- iterated substitution + lemmas -}
  field
    super    : Lemmas₀ tms simple

  open Lemmas₀ super public
  open Unifiers tms simple

  {- iterated to parallel substitutions -}
  par : ∀ {n m}(ρ : Sub T n m) → Par.Sub T n m
  par ρ = tabulate (asub ρ)

  private
    _[↦_] : ∀ {n m} → T n → Sub T n m → T m
    _[↦_] = λ t ρ → t par-/ (par ρ)

  {- useful parallel substitutions -}
  wk-at : ∀ {n} → Fin (ℕ.suc n) → Par.Sub T n (ℕ.suc n)
  wk-at x = tabulate (var ∘ punchIn x)

  sub_for_ : ∀ {n} → T n → Fin (ℕ.suc n) → Par.Sub T (ℕ.suc n) n
  sub t for x = tabulate (t for x)

  {- lemma about looking up in a converted iterated substitution -}
  lookup-par : ∀ {n m} x (ρ : Sub T n m) → lookup x (par ρ) ≡ asub ρ x
  lookup-par x ρ = lookup∘tabulate (asub ρ) x

  field
    /-par : ∀ {n m} (ρ : Sub T n m) t → (t / ρ) ≡ t [↦ ρ ]

  var-/-par : ∀ {n m} x (ρ : Sub T n m) → (var x) [↦ ρ ] ≡ asub ρ x
  var-/-par x ρ = begin
    var x par-/ (par ρ)
    ≡⟨ var-/ ⟩ lookup x (par ρ)
    ≡⟨ lookup-par x ρ ⟩ asub ρ x ∎

  var-asnoc-step : ∀ {n m} x t (ρ : Sub T n m) → (var x) [↦ (ρ asnoc t / x) ] ≡ t [↦ ρ ]
  var-asnoc-step x t ρ = begin
    var x par-/ (par (ρ asnoc t / x))
    ≡⟨ var-/-par x (ρ asnoc t / x) ⟩ asub (ρ asnoc t / x) x
    ≡⟨ cong (bind (asub ρ)) (t-for-x x) ⟩ bind (asub ρ) t
    ≡⟨ /-par ρ t ⟩ t par-/ par ρ ∎

  tabulate-⊙ : ∀ {n m x}{f : Fin x → T n}(ρ : Par.Sub T n m) → tabulate f par-⊙ ρ ≡ tabulate ((_par-/ ρ) ∘ f)
  tabulate-⊙ {f = f} ρ = sym (tabulate-∘ (_par-/ ρ) f)

  var-wk-at : ∀ {n}{x : Fin (ℕ.suc n)} y → (var y) par-/ wk-at x ≡ var (punchIn x y)
  var-wk-at y = trans var-/ (lookup∘tabulate (var ∘ punchIn _) y)

  •-rev-wk : ∀ {n m l} x (ρ : Sub T n m)(φ : Sub T m l) → (asub (ρ ⊙ φ)) (punchIn⋆ ρ x) ≡ (asub φ x)
  •-rev-wk x anil φ = refl
  •-rev-wk x (ρ asnoc t / y) φ = begin
      asub ((ρ ⊙ φ) asnoc t / y) (punchIn⋆ (ρ asnoc t / y) x)
    ≡⟨⟩
      asub ((ρ ⊙ φ) asnoc t / y) (punchIn y (punchIn⋆ ρ x))
    ≡⟨ asnoc-punchIn (ρ ⊙ φ) y _ t ⟩
      asub (ρ ⊙ φ) (punchIn⋆ ρ x)
    ≡⟨ •-rev-wk x ρ φ ⟩
      asub φ x ∎

  {- asnoc-punchin also disappears in the par version -}
  wk-at-vanishes : ∀ {v w}(ρ : Sub T v w) x t → wk-at x par-⊙ par (ρ asnoc t / x) ≡ par ρ
  wk-at-vanishes ρ x t =
    begin
        wk-at x par-⊙ par (ρ asnoc t / x)
      ≡⟨ tabulate-⊙ (par (ρ asnoc t / x)) ⟩
        tabulate ((_par-/ (par (ρ asnoc t / x))) ∘ var ∘ punchIn x)
      ≡⟨ tabulate-cong (λ y → var-/-par (punchIn x y) (ρ asnoc t / x)) ⟩
        tabulate (asub (ρ asnoc t / x) ∘ (punchIn x))
      ≡⟨ tabulate-cong (λ y → asnoc-punchIn ρ x y t) ⟩
        par ρ ∎

  {- one can push through `wk-at x` on punchIn⋆ to an instance of `punchIn x` -}
  rev-wk-⊙-wk-at : ∀ {n m}(φ : Sub T m n){x} →
                   tabulate (var ∘ punchIn⋆ φ) par-⊙ wk-at x ≡
                   tabulate (var ∘ punchIn x ∘ punchIn⋆ φ)
  rev-wk-⊙-wk-at φ {x} =
    begin
      tabulate (var ∘ (punchIn⋆ φ)) par-⊙ (wk-at x)
    ≡⟨ tabulate-⊙ (wk-at x) ⟩
      tabulate ((_par-/ (wk-at x)) ∘ var ∘ (punchIn⋆ φ))
    ≡⟨ tabulate-cong (var-wk-at ∘ (punchIn⋆ φ)) ⟩
      tabulate (var ∘ (Fin.punchIn x) ∘ (punchIn⋆ φ)) ∎
