module Data.Fin.Subset.Disjoint.Properties where

open import Function
open import Data.Nat
open import Data.Unit
open import Data.Vec as Vec hiding (_++_; _∈_)
open import Data.List as List hiding (zipWith; foldr)
open import Data.Bool
open import Data.Bool.Properties
open import Data.Product
open import Data.Sum as Sum
open import Data.Empty hiding (⊥)
open import Relation.Binary.PropositionalEquality

open import Data.Fin hiding (_-_)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Fin.Subset.Disjoint

module _ where

  q-p∪p : ∀ {n}{p q : Subset n} → q ⊆ p → (p ⊝ q) ∪ q ≡ p
  q-p∪p {p = []} {[]} s = refl
  q-p∪p {p = x ∷ p} {outside ∷ q} s rewrite ∨-identityʳ x =
    cong₂ _∷_ refl (q-p∪p (drop-∷-⊆ s))
  q-p∪p {p = outside ∷ p} {true ∷ q} s with s here
  ... | ()
  q-p∪p {p = true ∷ p} {true ∷ q} s = cong₂ _∷_ refl (q-p∪p (drop-∷-⊆ s))

  ⊆-∪-cong : ∀ {n}{x y x' y' : Subset n} → x ⊆ x' → y ⊆ y' → (x ∪ y) ⊆ (x' ∪ y')
  ⊆-∪-cong p q t with x∈p∪q⁻ _ _ t
  ... | inj₁ z = p⊆p∪q _ (p z)
  ... | inj₂ z = q⊆p∪q _ _ (q z)

-- properties of disjoint subsets x ◆ y
module _ where

  ◆-tail : ∀ {n} x y {xs ys : Subset n} → (x ∷ xs) ◆ (y ∷ ys) → xs ◆ ys
  ◆-tail _ _ p (x , x∈xs) = p (suc x , there x∈xs)

  ◆-∷ : ∀ {n} x y {xs ys : Subset n} → (T (not (x ∧ y))) → xs ◆ ys → (x ∷ xs) ◆ (y ∷ ys)
  ◆-∷ true true () q
  ◆-∷ true    outside p q (_ , there snd) = q (_ , snd)
  ◆-∷ outside _       p q (_ , there snd) = q (_ , snd)

  ◆-comm : ∀ {n} {x y : Subset n} → x ◆ y → y ◆ x
  ◆-comm {x = x}{y} = subst Empty (∩-comm x y)

  ◆-⊆-left : ∀ {n}{x y z : Subset n} → x ⊆ y → y ◆ z → x ◆ z
  ◆-⊆-left w d (e , e∈x∩z) = let (e∈x , e∈z) = (x∈p∩q⁻ _ _ e∈x∩z) in d (e , x∈p∩q⁺ ((w e∈x) , e∈z))

  ◆-⊆-right : ∀ {n}{x y z : Subset n} → x ⊆ z → y ◆ z → y ◆ x
  ◆-⊆-right w d = ◆-comm (◆-⊆-left w (◆-comm d))

  ◆-∉ : ∀ {n}{x y : Subset n}{i} → x ◆ y → i ∈ x → i ∉ y
  ◆-∉ {y = outside ∷ y} p here = λ ()
  ◆-∉ {y = inside ∷ y} p here = λ _ → p (zero , here)
  ◆-∉ {y = _ ∷ ys} p (there {y = y} q) (there z) =
    ◆-∉ (λ where (i , i∈ys) → p (suc i , there i∈ys)) q z

  ⊆-◆ : ∀ {n}{x y z : Subset n} → x ⊆ y → x ◆ z → x ⊆ y ⊝ z
  ⊆-◆ {x = .(true ∷ _)} {_ ∷ _} {outside ∷ zs} p x◆z here with p here
  ... | here = here
  ⊆-◆ {x = .(true ∷ _)} {_ ∷ _} {inside  ∷ zs} p x◆z here = ⊥-elim (◆-∉ x◆z here here)
  ⊆-◆ {x = .(_ ∷ _)} {y ∷ ys} {z ∷ zs} p x◆z (there i∈x) =
    there (⊆-◆ (drop-∷-⊆ p) (◆-tail _ z x◆z) i∈x)

  ◆-∪ : ∀ {n}{x y z : Subset n} → x ◆ y → x ◆ z → x ◆ (y ∪ z)
  ◆-∪ x◆y x◆z (i , i∈x∩y∪z) with x∈p∪q⁻ _ _ (proj₂ (x∈p∩q⁻ _ _ i∈x∩y∪z))
  ... | inj₁ i∈y = x◆y (i , (x∈p∩q⁺ (proj₁ (x∈p∩q⁻ _ _ i∈x∩y∪z) , i∈y)))
  ... | inj₂ i∈z = x◆z (i , (x∈p∩q⁺ (proj₁ (x∈p∩q⁻ _ _ i∈x∩y∪z) , i∈z)))

  ◆-- : ∀ {n}(x y : Subset n) → x ◆ (y ⊝ x)
  ◆-- xs ys (zero , p) with x∈p∩q⁻ _ _ p
  ◆-- (.true ∷ _) (outside ∷ _) (zero , p) | here , ()
  ◆-- (.true ∷ _) (true ∷ _)    (zero , p) | here , ()
  ◆-- (_ ∷ xs) (_ ∷ ys) (suc e , there p) = ◆-- xs ys (e , p)

  ◆-⊥ : ∀ {n} {x : Subset n} → x ◆ ⊥
  ◆-⊥ (i , snd) = ∉⊥ (subst (λ s → i ∈ s) (proj₂ ∩-zero _) snd)

-- properties of disjoint covers
module _ where

  ∪-≡-inversion : ∀ {n}{xs ys zs : Subset n} x y {z} → (x ∷ xs) ∪ (y ∷ ys) ≡ (z ∷ zs) → xs ∪ ys ≡ zs
  ∪-≡-inversion _ _ refl = refl

  covered : ∀ {n}{xs ys zs : Subset n}{z} → xs ⊎ ys cover zs → z ∈ zs → (z ∈ xs) ⊎ (z ∈ ys)
  covered {xs = []} {[]} (xs◆ys , refl) ()
  covered {xs = x ∷ xs}{y ∷ ys} (xs◆ys , eq) (there e) =
    Sum.map there there (covered (◆-tail x y xs◆ys , ∪-≡-inversion x y eq) e)
  covered {xs = inside  ∷ xs} {_       ∷ ys} (xs◆ys , eq) here = inj₁ here
  covered {xs = outside ∷ xs} {inside  ∷ ys} (xs◆ys , eq) here = inj₂ here
  covered {xs = outside ∷ xs} {outside ∷ ys} (xs◆ys , ()) here

-- properties of disjoint unions z of xs (xs ⨄ z)
module _ where

  -- append for disjoint disjoint-unions of subsets
  -- ++-⨄ : ∀ {n}{xs ys}{x y : Subset n} → xs ⨄ x → ys ⨄ y → (x ◆ y) → (xs ++ ys) ⨄ (x ∪ y)
  -- ++-⨄ {x = x}{y} [] q d rewrite ∪-identityˡ y = q
  -- ++-⨄ {y = y} (_∷_ {x = x}{z} x◆z xs⊎y) ys⊎z x∪z⊎y rewrite ∪-assoc x z y =
  --   (◆-∪ x◆z (◆-⊆-left (p⊆p∪q z) x∪z⊎y)) ∷ (++-⨄ xs⊎y ys⊎z (◆-⊆-left (q⊆p∪q x z) x∪z⊎y))

  -- ⨄-trans : ∀ {n}{xs ys}{x y : Subset n} → xs ⨄ x → (x ∷ ys) ⨄ y → (xs ++ ys) ⨄ (x ∪ y)
  -- ⨄-trans {x = x}{y} xs▰x (_∷_ {y = z} x◆y ys▰y) rewrite sym (∪-assoc x x z) =
  --   subst (λ x → _ ⨄ (x ∪ z)) (sym (∪-idem x)) (++-⨄ xs▰x ys▰y x◆y)

-- decidability of disjointness
module _ where

  open import Relation.Nullary
  open import Relation.Nullary.Decidable as DecM

  Nonempty-not-here : ∀ {n}{xs : Subset n} → Nonempty (outside ∷ xs) → Nonempty xs
  Nonempty-not-here (_ , there snd) = _ , snd

  Nonempty-there : ∀ {n}{xs : Subset n} → Nonempty xs → Nonempty (outside ∷ xs)
  Nonempty-there (_ , p) = _ , there p

  _◆?_ : ∀ {n}(xs ys : Subset n) → Dec (xs ◆ ys)
  [] ◆? [] = yes (λ ())
  (outside ∷ xs) ◆? (_ ∷ ys) = DecM.map′
    (◆-∷ outside inside tt)
    (◆-tail outside inside)
    (xs ◆? ys)
  (inside ∷ xs) ◆? (outside ∷ ys) = DecM.map′
    (◆-∷ inside outside tt)
    (◆-tail inside outside)
    (xs ◆? ys)
  (inside ∷ xs) ◆? (inside ∷ ys) = no (_$ (_ , here))
