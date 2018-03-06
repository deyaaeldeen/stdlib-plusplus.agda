open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

module Category.Monad.Monotone.Reader {ℓ}(pre : Preorder ℓ ℓ ℓ)(E : Pred (Preorder.Carrier pre) ℓ) where

open Preorder pre renaming (Carrier to I; _∼_ to _≤_; refl to ≤-refl)

open import Relation.Unary.Monotone pre
open import Relation.Unary.PredicateTransformer using (Pt)
open import Data.Product
open import Function
open import Level hiding (lift)
open import Category.Monad
open import Category.Monad.Monotone.Identity pre
open import Category.Monad.Monotone pre

ReaderT : Pt I ℓ → Pt I ℓ
ReaderT M P = λ i → E i → M P i

Reader : Pt I ℓ
Reader = ReaderT Identity

record ReaderMonad (M : Pt I ℓ) : Set (suc ℓ) where
  field
    ask    : ∀ {i} → M E i
    reader : ∀ {P} → (E ⇒ P) ⊆ M P
    local  : ∀ {P} → (E ⇒ E) ⊆ (M P ⇒ M P)

  asks : ∀ {A} → (E ⇒ A) ⊆ M A
  asks = reader

open ReaderMonad ⦃...⦄ public

module _ {M}⦃ Mon : RawMPMonad M ⦄ where
  private module M = RawMPMonad Mon

  module _ ⦃ mono : Monotone E ⦄ where
    instance
      open RawMPMonad
      reader-monad : RawMPMonad (ReaderT M)
      return reader-monad x e = M.return x
      _≥=_  reader-monad m f e = m e M.≥= λ i≤j px → f i≤j px (wk i≤j e)

      open ReaderMonad
      reader-monad-ops : ReaderMonad (ReaderT M)
      ask reader-monad-ops e = M.return e
      reader reader-monad-ops f e = M.return (f e)
      local reader-monad-ops f c e = c (f e)

  lift-reader : ∀ {P} → M P ⊆ ReaderT M P
  lift-reader z _ = z
