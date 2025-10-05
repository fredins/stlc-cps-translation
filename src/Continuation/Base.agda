
module Continuation.Base where

open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Function using (_∘_; id)
open import Level using (Level) 

private variable
  ℓ : Level
  α : Set ℓ
  A B : Set ℓ

record Cont (α : Set ℓ) (A : Set ℓ) : Set ℓ where
  field
    runCont : (A → α) → α

open Cont

map : (A → B) → Cont α A  → Cont α B
map f k .runCont g = k .runCont (g ∘ f)

pure : A → Cont α A
pure x .runCont k = k x

ap : Cont α (A → B) → Cont α A → Cont α B
ap kf k .runCont g = kf .runCont λ f → k .runCont (g ∘ f)

infixl 1 _>>=_

_>>=_ : Cont α A → (A → Cont α B) → Cont α B
(k >>= f) .runCont g = k .runCont λ x → f x .runCont g

functor : RawFunctor {ℓ} (Cont α)
functor = record { _<$>_ = map }

applicative : RawApplicative {ℓ} (Cont α)
applicative = record
  { rawFunctor = functor
  ; pure = pure
  ; _<*>_ = ap
  }

monad : RawMonad {ℓ} (Cont α)
monad = record
  { rawApplicative = applicative
  ; _>>=_ = _>>=_
  }

open import Data.Nat using (zero; suc; ℕ; _+_) 
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

example : Cont α ℕ
example = 
  pure 4 .runCont λ x →
  pure 8 .runCont λ y →
  pure (x + y)

_ : example .runCont id ≡ 12
_ = refl

example-monads : Cont α ℕ
example-monads = 
  pure 4 >>= λ x →
  pure 8 >>= λ y → 
  pure (x + y)

example-do-notation : Cont α ℕ
example-do-notation = do 
  x ← pure 4
  y ← pure 8
  pure (x + y)
