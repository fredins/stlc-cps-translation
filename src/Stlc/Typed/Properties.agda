
module Stlc.Typed.Properties where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
  using (Star)
  renaming (ε to []; _◅_ to _∷_)
import Relation.Binary.PropositionalEquality as PE
open PE.≡-Reasoning
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

open import Stlc.Untyped
open import Stlc.Typed

private variable
  m n  : ℕ
  A B  : Type
  t t′ t₁ t₁′ t″ : Term _
  Γ    : Con _
  x    : Fin _

normal-do-not-reduce : Γ ⊢ t ⇒ t′ ∷ A → ¬ (Normal t)
normal-do-not-reduce (β-lam x x₁) (neutral (· ()))
normal-do-not-reduce (ξ-lam x) (lam y) = normal-do-not-reduce x y
normal-do-not-reduce (ξ-·ₗ x x₁) y = normal-do-not-reduce x₁ (neutral x)
normal-do-not-reduce (ξ-·ᵣ (neutral x) x₁) (neutral (· y)) = {! !}
normal-do-not-reduce (ξ-suc x) (suc y) = normal-do-not-reduce x y

red-det : Γ ⊢ t ⇒ t′ ∷ A → Γ ⊢ t ⇒ t″ ∷ A → t′ PE.≡ t″
red-det (β-lam x x₁) (β-lam y y₁) = PE.refl
red-det (β-lam p p₁) (ξ-·ᵣ normal q) = ⊥-elim {! !}


red-det (ξ-lam p) q = {! !}
red-det (ξ-·ₗ x p) q = {! !}
red-det (ξ-·ᵣ x p) q = {! !}
red-det (ξ-suc p) q = {! !}
