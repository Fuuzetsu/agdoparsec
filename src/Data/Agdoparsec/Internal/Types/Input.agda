module Data.Agdoparsec.Internal.Types.Input where

open import Algebra
open import Function
open import Algebra.FunctionProperties using (Op₂; Associative)

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
open import Algebra.Structures
open import Data.Product using (_,_; proj₁; proj₂)

record Input {ℓ} (τ : Set ℓ) : Set ℓ where
  constructor I
  field
    unI : τ

private
  lift-Op₂ : ∀ {ℓ} {A : Set ℓ} → Op₂ A → Op₂ (Input A)
  lift-Op₂ _∙_ a b = I (Input.unI a ∙ Input.unI b)

  lift-Associative : ∀ {ℓ} {A : Set ℓ} {∙ : Op₂ A}
     → Associative _≡_ ∙ → Associative _≡_ (lift-Op₂ ∙)
  lift-Associative a∙ =
     λ x y z → cong I (a∙ (Input.unI x) (Input.unI y) (Input.unI z))

  lift-IsSemigroup : ∀ {ℓ} {A : Set ℓ} {∙ : Op₂ A}
     → IsSemigroup _≡_ ∙ → IsSemigroup _≡_ (lift-Op₂ ∙)
  lift-IsSemigroup {∙ = _∙_} a =
     record { isEquivalence = isEquivalence
            ; assoc = lift-Associative {∙ = _∙_} (IsSemigroup.assoc a)
            ; ∙-cong = cong₂ (lift-Op₂ _∙_)
            }

  lift-IsMonoid : ∀ {ℓ} {A : Set ℓ} {∙ : Op₂ A} {ε : A}
     → IsMonoid _≡_ ∙ ε → IsMonoid _≡_ (lift-Op₂ ∙) (I ε)
  lift-IsMonoid a =
     record { isSemigroup = lift-IsSemigroup (IsMonoid.isSemigroup a)
            ; identity = cong I ∘ proj₁ (IsMonoid.identity a) ∘ Input.unI ,
                         cong I ∘ proj₂ (IsMonoid.identity a) ∘ Input.unI
            }

monoid : ∀ {ℓ} {A : Set ℓ} {∙ : Op₂ A} {ε : A}
   → IsMonoid _≡_ ∙ ε → Monoid ℓ ℓ
monoid {_} {A} {∙} {ε} a = record
  { Carrier = Input A
  ; _≈_ = _≡_
  ; _∙_ = lift-Op₂ ∙
  ; ε = I ε
  ; isMonoid = lift-IsMonoid a
  }
