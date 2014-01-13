module Data.Agdoparsec.Internal.Types where

open import Data.Agdoparsec.Internal.Types.Input hiding (monoid)
open import Data.Agdoparsec.Internal.Types.Added hiding (monoid)
open import Data.Agdoparsec.Internal.Types.More hiding (monoid)
open import Function

open import Data.List using (_++_; List; [])
open import Data.Char using (Char)

String : Set
String = List Char

data IResult (τ : Set) (r : Set) : Set where
  Fail : τ → List String → String → IResult τ r
  Partial : (τ → IResult τ r) → IResult τ r
  Done : τ → r → IResult τ r

Failure : Set → Set → Set
Failure τ r = Input τ → Added τ → More → List String → String → IResult τ r

Success : Set → Set₁ → Set → Set₁
Success τ α r = Input τ → Added τ → More → α → IResult τ r

record Parser (τ : Set) (α : Set₁) : Set₁ where
  constructor mkParser
  field
    runParser : ∀ {r} → Input τ → Added τ → More → Failure τ r
              → Success τ α r → IResult τ r

module ParserInstances where
  open import Algebra using (Monoid)
  open import Algebra.Structures using (IsMonoid)
  open import Relation.Binary.PropositionalEquality
  open import Algebra.FunctionProperties using (Op₂)

  bindP : ∀ {τ α β} → Parser τ α → (α → Parser τ β) → Parser τ β
  bindP m g = mkParser $ λ i₀ a₀ m₀ kf ks → runParser m i₀ a₀ m₀ kf $
    λ i₁ a₁ m₁ a → runParser (g a) i₁ a₁ m₁ kf ks
    where
      open Parser

  returnP : ∀ {τ α} → α → Parser τ α
  returnP a = mkParser (λ i₀ a₀ m₀ kf ks → ks i₀ a₀ m₀ a)

  open import Data.String using (toList)

  failDesc : ∀ {τ α} → String → Parser τ α
  failDesc err = mkParser (λ i₀ a₀ m₀ kf ks → kf i₀ a₀ m₀ [] msg)
    where
      msg = toList "Failed reading: " ++ err

  open import Category.Monad
  open import Level

  noAdds : ∀ {τ ε} → {r : Set}
         → {∙ : Op₂ {zero} (Added τ)} → {m : IsMonoid _≡_ ∙ ε}
         → Input τ → Added τ → More → (Input τ → Added τ → More → r) → r
  noAdds {ε = ε} i₀ a₀ m₀ f = f i₀ ε m₀

  addS : ∀ {τ εa εi} → {r : Set}
       → {_a∙_ : Op₂ {zero} (Added τ)} {ma : IsMonoid _≡_ _a∙_ εa}
       → {_i∙_ : Op₂ (Input τ)} {mi : IsMonoid _≡_ _i∙_ εi}
       → Input τ → Added τ → More
       → Input τ → Added τ → More
       → (Input τ → Added τ → More → r) → r
  addS {_a∙_ = _a∙_} {_i∙_ = _i∙_} i₀ a₀ m₀ _ a₁ m₁ f =
    f (i₀ i∙ I (Added.unA a₁)) (a₀ a∙ a₁) (m₀ ∙ m₁)
    where
      open Algebra.Monoid Data.Agdoparsec.Internal.Types.More.monoid

  plus : ∀ {τ α εa εi}
       → {_a∙_ : Op₂ (Added τ)} {ma : IsMonoid _≡_ _a∙_ εa}
       → {_i∙_ : Op₂ (Input τ)} {mi : IsMonoid _≡_ _i∙_ εi}
       → Parser τ α → Parser τ α → Parser τ α
  plus {_a∙_ = _a∙_} {ma = ma} {mi = mi} a b = mkParser $ λ i₀ a₀ m₀ kf ks →
    let kf′ = λ i₁ a₁ m₁ _ _ → addS {ma = ma} {mi = mi} i₀ a₀ m₀ i₁ a₁ m₁ $
                λ i₂ a₂ m₂ → Parser.runParser b i₂ a₂ m₂ kf ks
        ks′ = λ i₁ a₁ m₁ → ks i₁ (a₀ a∙ a₁) m₁
    in noAdds {m = ma} i₀ a₀ m₀ $
         λ i₂ a₂ m₂ → Parser.runParser a i₂ a₂ m₂ kf′ ks′

  monad : ∀ {τ} → RawMonad (Parser τ)
  monad =  record
    { return = returnP
    ; _>>=_ = bindP
    }

  monadZero : ∀ {τ} → RawMonadZero (Parser τ)
  monadZero = record
    { monad = monad
    ; ∅ = failDesc $ toList "mzero"
    }

  monadPlus : ∀ {τ ε}
            → {_∙_ : Op₂ τ} {ma : IsMonoid _≡_ _∙_ ε}
            → RawMonadPlus (Parser τ)
  monadPlus {ma = ma} = record
    { monadZero = monadZero
    ; _∣_ = plus {ma = isMonoid m₁} {mi = isMonoid m₂}
    }
    where
      open Algebra.Monoid
      m₁ = Data.Agdoparsec.Internal.Types.Added.monoid ma
      m₂ = Data.Agdoparsec.Internal.Types.Input.monoid ma

  monoid : {α : Set₁} {τ : Set} {_∙_ : Op₂ τ} {ε : τ}
         → IsMonoid _≡_ _∙_ ε → Monoid (suc zero) (suc zero)
  monoid {α} {τ} {_∙_} {ε} m = record
    { Carrier = Parser τ α
    ; _≈_ = _≡_
    ; _∙_ = _<>_
    ; ε = failDesc (toList "mempty")
    ; isMonoid = record
        { isSemigroup = record
            { isEquivalence = isEquivalence
            ; assoc = postulated-assoc
            ; ∙-cong = cong₂ _<>_
            }
        ; identity = postulated-lidentity , postulated-identity
        }
    }
    where
      open import Data.Product using (_,_; proj₁; proj₂)
      open Algebra.Monoid hiding (isEquivalence; refl; sym; trans)

      m₁ = Data.Agdoparsec.Internal.Types.Added.monoid m
      m₂ = Data.Agdoparsec.Internal.Types.Input.monoid m

      infixl 7 _<>_
      _<>_ = plus {ma = isMonoid m₁} {mi = isMonoid m₂}

      open import Algebra.FunctionProperties _≡_
      open Added
      open Input

      -- Temporary clutch while I think and do other stuff.
      postulate
        postulated-assoc : Associative _<>_
        postulated-identity : RightIdentity (failDesc (toList "mempty")) _<>_
        postulated-lidentity : LeftIdentity (failDesc (toList "mempty")) _<>_

      -- leftid : LeftIdentity (failDesc (toList "mempty")) _<>_
      -- leftid (mkParser runParser) = {!!}
      --   where
      --     open ≡-Reasoning

      -- passoc : Associative _<>_
      -- passoc x y z = begin
      --   (x <> y) <> z ≡⟨ {!!} ⟩
      --   x <> (y <> z) ∎
      --   where
      --     open ≡-Reasoning

      -- LeftIdentity was just not type checking. For a second there, I felt a
      -- bit on the http://fuuzetsu.co.uk/images/doesnttypecheck.gif side there…
      -- pidentity : RightIdentity (failDesc (toList "mempty")) _<>_
      -- pidentity (mkParser runParser) = {!!}
        -- begin
        -- mkParser runParser <> failDesc msg ≡⟨ refl ⟩
        -- mkParser (λ i₀ a₀ m₀ kf ks → noAdds {m = {!!}} i₀ a₀ m₀ fooz) <> failDesc msg ≡⟨ {!!} ⟩
        -- mkParser runParser ∎
        -- where
        --   fooz : ∀ {r} → Input τ → Added τ → More → IResult τ r
        --   fooz = {!!}

        --   msg = toList "mempty"
        --   open ≡-Reasoning
        --   open import Data.List using (_∷_)
