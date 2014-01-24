module Data.Agdoparsec.Internal.Types where

open import Data.Agdoparsec.Internal.Types.Input hiding (monoid)
open import Data.Agdoparsec.Internal.Types.Added hiding (monoid)
open import Data.Agdoparsec.Internal.Types.More hiding (monoid; _<>_)
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
  noAdds {ε = ε} i₀ _ m₀ f = f i₀ ε m₀

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
        ; identity = leftid , postulated-identity
        }
    }
    where
      open import Data.Product using (_,_; proj₁; proj₂)
      open Algebra.Monoid hiding (isEquivalence; refl; sym; trans)

      m₁ = Data.Agdoparsec.Internal.Types.Added.monoid m
      m₂ = Data.Agdoparsec.Internal.Types.Input.monoid m

      amonoid = m₁
      imonoid = m₂

      infixl 7 _<>_
      _<>_ = plus {ma = isMonoid m₁} {mi = isMonoid m₂}

      open import Algebra.FunctionProperties _≡_
      open Added
      open Input

      -- Temporary clutch while I think and do other stuff.
      postulate
        postulated-assoc : Associative _<>_
        postulated-identity : RightIdentity (failDesc (toList "mempty")) _<>_

        ext : ∀ {a b} → Extensionality a b

      cong₅ : {a b c d e f : Level} {A : Set a} {B : Set b} {C : Set c}
            → {D : Set d} {E : Set e} {F : Set f}
            → {ax ay : A} {bx by : B} {cx cy : C} {dx dy : D} {ex ey : E}
            → (g : A → B → C → D → E → F)
            → ax ≡ ay → bx ≡ by → cx ≡ cy → dx ≡ dy → ex ≡ ey
            → g ax bx cx dx ex ≡ g ay by cy dy ey
      cong₅ f refl refl refl refl refl = refl

      cong₄ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c}
            → {D : Set d} {E : Set e}
            → {ax ay : A} {bx by : B} {cx cy : C} {dx dy : D}
            → (g : A → B → C → D → E)
            → ax ≡ ay → bx ≡ by → cx ≡ cy → dx ≡ dy
            → g ax bx cx dx ≡ g ay by cy dy
      cong₄ f refl refl refl refl = refl

      cong₃ : {a b c d : Level} {A : Set a} {B : Set b} {C : Set c}
            → {D : Set d}
            → {ax ay : A} {bx by : B} {cx cy : C}
            → (g : A → B → C → D)
            → ax ≡ ay → bx ≡ by → cx ≡ cy
            → g ax bx cx ≡ g ay by cy
      cong₃ f refl refl refl = refl


      open Data.Agdoparsec.Internal.Types.More renaming (_<>_ to _<>m_)


      err = toList "Failed reading: mempty"

      Iid : ∀ {x} → I (unI x ∙ ε) ≡ x
      Iid {x} = (proj₂ ∘ IsMonoid.identity $ isMonoid m₂) x

      Aid : ∀ {x} → A (unA x ∙ ε) ≡ x
      Aid {x} = (proj₂ ∘ IsMonoid.identity $ isMonoid m₁) x

      Mid : ∀ {x} → x <>m x ≡ x
      Mid {Complete} = refl
      Mid {Incomplete} = refl


      postulate
        impExt : {f g : ∀ {r} → Input τ → Added τ → More
                      → Failure τ r → Success τ α r → IResult τ r}
               → (∀ r′ i a m kf ks → f {r′} i a m kf ks ≡ g {r′} i a m kf ks)
               → (λ {r} i a m kf ks → f {r} i a m kf ks)
                 ≡ (λ {r} i a m kf ks → g {r} i a m kf ks)


      unId : ∀ p → ∀ {r i₀ a₀ m₀} → {kf : Failure τ r} → ∀ {ks}
           → Parser.runParser p {r} (I (unI i₀ ∙ ε)) (A (unA a₀ ∙ ε))
                              (m₀ <>m m₀) kf ks
            ≡ Parser.runParser p i₀ a₀ m₀ kf ks
      unId p = cong₅ (Parser.runParser p) Iid Aid Mid refl refl

      cong-mkParser : {f g : ∀ {r} → Input τ → Added τ → More
                                   → Failure τ r → Success τ α r
                                   → IResult τ r}
                    → (∀ r′ i a m kf ks → f {r′} i a m kf ks
                                          ≡ g {r′} i a m kf ks)
                    → mkParser f ≡ mkParser g
      cong-mkParser p = cong mkParser (impExt p)

      -- cong-runParser : ∀ p → {f g : ∀ {r} → Input τ → Added τ → More
      --                        → Failure τ r → Success τ α r
      --                        → IResult τ r}
      --                → (∀ r′ i a m kf ks → f {r′} i a m kf ks
      --                  ≡ g {r′} i a m kf ks)
      --                → Parser.runParser p f ≡ Parser.runParser p g
      -- cong-runParser p = cong Parser.runParser {!!}

      leftid : LeftIdentity (failDesc (toList "mempty")) _<>_
      leftid p = begin
        failDesc (toList "mempty") <> p ≡⟨ refl ⟩
        mkParser (λ i₀ a₀ m₀ kf ks → kf i₀ a₀ m₀ [] err) <> p ≡⟨ refl ⟩
        mkParser
          (λ i₀ a₀ m₀ kf ks →
            Parser.runParser p (I (unI i₀ ∙ ε)) (A (unA a₀ ∙ ε)) (m₀ <>m m₀) kf
            ks) ≡⟨ cong-mkParser (λ r i₀ a₀ m₀ kf ks → unId p) ⟩
        mkParser
          (λ i₀ a₀ m₀ kf ks →
            Parser.runParser p i₀ a₀ m₀ kf ks)
        ≡⟨ cong-mkParser (λ r i₀ a₀ m₀ kf ks → refl) ⟩
        p ∎
        where
          open ≡-Reasoning


      -- rightid : RightIdentity (failDesc (toList "mempty")) _<>_
      -- rightid p =
      --   begin
      --   p <> errp ≡⟨ refl ⟩
      --   mkParser
      --     (λ {r} i₀ a₀ m₀ kf ks →
      --        noAdds {m = isMonoid amonoid} i₀ a₀ m₀ $
      --        (λ i₂ a₂ m₃ →
      --           Parser.runParser p i₂ a₂ m₃
      --           (λ i₁ a₁ m₄ _ _ →
      --              addS {ma = isMonoid amonoid} {mi = isMonoid imonoid} i₀ a₀ m₀ i₁ a₁ m₄
      --              (λ i₃ a₃ m₅ → Parser.runParser errp i₃ a₃ m₅ kf ks))
      --           (λ i₁ a₁ → ks i₁ (a₀ a∙ a₁)))) ≡⟨ {!!} ⟩
      --   p ∎
      --   where
      --     open ≡-Reasoning
      --     _a∙_ = Monoid._∙_ amonoid
      --     _i∙_ = Monoid._∙_ imonoid

      --     errm = toList "Failed reading: mempty"
      --     errp = failDesc (toList "mempty")

      --     -- ksp : ∀ r ks a₀ → (λ i₁ a₁ → ks i₁ (A (unA a₀ ∙ unA a₁))) ≡ ks
      --     -- ksp r ks (A unA) = {!cong !}


      --     kfp : ∀ {r} i₀ a₀ m₀ → (kf : Failure τ r)
      --         → (λ i₁ a₁ m₁ kf₁ ks₁ → kf (I (unI i₀ ∙ unA a₁))
      --                                    (A (unA a₀ ∙ unA a₁))
      --                                    (m₀ <>m m₁) [] errm)
      --           ≡ λ i₁ a₁ m₁ kf₁ ks₁ → kf i₁ a₁ m₁ kf₁ ks₁
      --     kfp i₀ a₀ m₀ kf = {!!}

          -- foo : {!!} → {!!} →  {!!} → {!!} → {!!} → {!!} → {!!} → {!!}
          -- foo = {!!}


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
