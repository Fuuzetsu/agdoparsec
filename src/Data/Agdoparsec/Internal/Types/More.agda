module Data.Agdoparsec.Internal.Types.More where

open import Algebra
open import Function
open import Algebra.FunctionProperties using (Op₂)

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
open import Algebra.Structures
open import Data.Product using (_,_; proj₁; proj₂)


data More : Set where
  Complete : More
  Incomplete : More

_<>_ : More → More → More
Complete <> _ = Complete
_ <> m = m

monoid : Monoid zero zero
monoid = record
  { Carrier = More
  ; _≈_ = _≡_
  ; _∙_ = _<>_
  ; ε = Incomplete
  ; isMonoid = record
      { isSemigroup = record
          { isEquivalence = isEquivalence
          ; assoc = λ { Complete _ _ → refl ; Incomplete _ _ → refl }
          ; ∙-cong = cong₂ _<>_
          }
      ; identity = (λ _ → refl) , λ { Complete → refl ; Incomplete → refl }
      }
  }
