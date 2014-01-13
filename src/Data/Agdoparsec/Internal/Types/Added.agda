module Data.Agdoparsec.Internal.Types.Added where

open import Algebra
open import Function
open import Algebra.FunctionProperties using (Op₂; Associative)

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
open import Algebra.Structures
open import Data.Product using (_,_; proj₁; proj₂)

record Added {ℓ} (τ : Set ℓ) : Set ℓ where
  constructor A
  field
    unA : τ

private
  lift-Op₂ : ∀ {ℓ} {A : Set ℓ} → Op₂ A → Op₂ (Added A)
  lift-Op₂ _∙_ a b = A (Added.unA a ∙ Added.unA b)

  lift-Associative : ∀ {ℓ} {A : Set ℓ} {∙ : Op₂ A}
     → Associative _≡_ ∙ → Associative _≡_ (lift-Op₂ ∙)
  lift-Associative a∙ =
     λ x y z → cong A (a∙ (Added.unA x) (Added.unA y) (Added.unA z))

  lift-IsSemigroup : ∀ {ℓ} {A : Set ℓ} {∙ : Op₂ A}
     → IsSemigroup _≡_ ∙ → IsSemigroup _≡_ (lift-Op₂ ∙)
  lift-IsSemigroup {∙ = _∙_} a =
     record { isEquivalence = isEquivalence
            ; assoc = lift-Associative {∙ = _∙_} (IsSemigroup.assoc a)
            ; ∙-cong = cong₂ (lift-Op₂ _∙_)
            }

  lift-IsMonoid : ∀ {ℓ} {A′ : Set ℓ} {∙ : Op₂ A′} {ε : A′}
                → IsMonoid _≡_ ∙ ε → IsMonoid _≡_ (lift-Op₂ ∙) (A ε)
  lift-IsMonoid a =
     record { isSemigroup = lift-IsSemigroup (IsMonoid.isSemigroup a)
            ; identity = cong A ∘ proj₁ (IsMonoid.identity a) ∘ Added.unA ,
                         cong A ∘ proj₂ (IsMonoid.identity a) ∘ Added.unA
            }

monoid : ∀ {ℓ} {A : Set ℓ} {∙ : Op₂ A} {ε : A}
   → IsMonoid _≡_ ∙ ε → Monoid ℓ ℓ
monoid {_} {τ} {∙} {ε} a = record
  { Carrier = Added τ
  ; _≈_ = _≡_
  ; _∙_ = lift-Op₂ ∙
  ; ε = A ε
  ; isMonoid = lift-IsMonoid a
  }
