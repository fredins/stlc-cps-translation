
module Stlc.Typed.Properties where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
  using (Star)
  renaming (ε to []; _◅_ to _∷_)
import Relation.Binary.PropositionalEquality as PE
open PE.≡-Reasoning
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)

open import Stlc.Untyped
open import Stlc.Untyped.Properties
open import Stlc.Typed

private variable
  m n        : ℕ
  x          : Fin _
  A B        : Type
  t t′ t″ t₁ : Term _
  Γ          : Con _
  ρ          : Wk _ _

-- Weakening preserves typing.

weakening-var-preserves-typing : 
  {Δ : Con m} {Γ : Con n} {ρ : Wk m n} → 
  ρ ∷ Δ ≤ Γ → 
  x ∷ A ∈ Γ → 
  wkVar ρ x ∷ A ∈ Δ
weakening-var-preserves-typing id x∈ = PE.subst (_∷ _ ∈ _) wkVar-id x∈
weakening-var-preserves-typing (↑ η) x∈ = 
  there (weakening-var-preserves-typing η x∈)
weakening-var-preserves-typing (⇑ η) here = here
weakening-var-preserves-typing (⇑ η) (there x∈) = 
  there (weakening-var-preserves-typing η x∈)

weakening-term-preserves-typing : 
  {Δ : Con m} {Γ : Con n} {ρ : Wk m n} → 
  ρ ∷ Δ ≤ Γ → 
  Γ ⊢ t ∷ A → 
  Δ ⊢ wk ρ t ∷ A
weakening-term-preserves-typing η (var x∈) = 
  var (weakening-var-preserves-typing η x∈)
weakening-term-preserves-typing η (lam ⊢t) = 
  lam (weakening-term-preserves-typing (⇑ η) ⊢t)
weakening-term-preserves-typing η (⊢t · ⊢t₁) = 
  weakening-term-preserves-typing η ⊢t · weakening-term-preserves-typing η ⊢t₁
weakening-term-preserves-typing η zero = zero
weakening-term-preserves-typing η (suc ⊢t) = 
  suc (weakening-term-preserves-typing η ⊢t)

-- Substitution preserves typing.

substitution-var-preserves-typing :
  {Γ : Con n} {Δ : Con m} {σ : Subst m n} → 
  Δ ⊢ˢ σ ∷ Γ → 
  x ∷ A ∈ Γ → 
  Δ ⊢ σ x ∷ A 
substitution-var-preserves-typing (⊢σ ▹ ⊢t) here = ⊢t
substitution-var-preserves-typing (⊢σ ▹ ⊢t) (there x∈) = 
  substitution-var-preserves-typing ⊢σ x∈

substitution-preserves-typing : 
  {Γ : Con n} {Δ : Con m} {σ : Subst m n} → 
  Δ ⊢ˢ σ ∷ Γ → 
  Γ ⊢ t ∷ A → 
  Δ ⊢ t [ σ ] ∷ A
substitution-preserves-typing ⊢σ (var x∈) = 
  substitution-var-preserves-typing ⊢σ x∈
substitution-preserves-typing ⊢σ (lam ⊢t) = 
  lam (substitution-preserves-typing (⊢σ ⇑ₜ) ⊢t)
substitution-preserves-typing ⊢σ (⊢t · ⊢t₁) = 
  substitution-preserves-typing ⊢σ ⊢t · substitution-preserves-typing ⊢σ ⊢t₁
substitution-preserves-typing ⊢σ zero = zero
substitution-preserves-typing ⊢σ (suc ⊢t) = 
  suc (substitution-preserves-typing ⊢σ ⊢t)

-- Neutral terms do not reduce.

no-ne-reduction : Γ ⊢ t ⇒ t′ ∷ A → ¬ (Ne t)
no-ne-reduction (β-red x x₂) (app ())
no-ne-reduction (·-cong x x₂) (app x₁) = no-ne-reduction x x₁

-- WHNFs do not reduce.

no-whnf-reduction : Γ ⊢ t ⇒ t′ ∷ A → ¬ (Whnf t)
no-whnf-reduction (β-red x x₂) (ne (app ()))
no-whnf-reduction (·-cong x x₂) (ne (app x₁)) = no-whnf-reduction x (ne x₁)

-- Reduction is deterministic.

reduction-det : {Γ : Con n} → Γ ⊢ t ⇒ t′ ∷ A → Γ ⊢ t ⇒ t″ ∷ B → t′ PE.≡ t″
reduction-det (β-red x x₂) (β-red x₁ x₃) = PE.refl
reduction-det (·-cong x x₂) (·-cong x₁ x₃) = PE.cong (_· _) (reduction-det x x₁)

-- Reduction to WHNF is deterministic.

reduction↘whnf-det : Γ ⊢ t ↘ t′ ∷ A → Γ ⊢ t ↘ t″ ∷ B → t′ PE.≡ t″
reduction↘whnf-det ([] , w) ([] , w₁) = PE.refl
reduction↘whnf-det ([] , w) (x₁ ∷ xs₁ , w₁) = ⊥-elim (no-whnf-reduction x₁ w)
reduction↘whnf-det (x ∷ xs ,  w) ([] , w₁) = ⊥-elim (no-whnf-reduction x w₁)
reduction↘whnf-det (x ∷ xs , w) (x₁ ∷ xs₁ , w₁) = 
  reduction↘whnf-det (xs , w) (PE.subst (_ ⊢_↘ _ ∷ _) (reduction-det x₁ x) (xs₁ , w₁)) 

-- Reduction is subsumed by equality.

equality-subsumes-reduction : Γ ⊢ t ⇒ t′ ∷ A → Γ ⊢ t ≡ t′ ∷ A
equality-subsumes-reduction (β-red ⊢t ⊢t₁) = β-red ⊢t ⊢t₁
equality-subsumes-reduction (·-cong r ⊢t) = 
  ·-cong (equality-subsumes-reduction r) (refl ⊢t)

mutual 
  -- Equality subject typing.

  equality-subject-typing : Γ ⊢ t ≡ t₁ ∷ A → Γ ⊢ t ∷ A
  equality-subject-typing (refl ⊢t) = ⊢t
  equality-subject-typing (sym ⊢≡) = equality-preserves-typing ⊢≡
  equality-subject-typing (trans ⊢≡ ⊢≡₁) = equality-subject-typing ⊢≡
  equality-subject-typing (β-red ⊢t ⊢t₁) = lam ⊢t · ⊢t₁
  equality-subject-typing (ρ-equal ⊢t ⊢t₁ ⊢≡) = ⊢t
  equality-subject-typing (·-cong ⊢≡ ⊢≡₁) = 
    equality-subject-typing ⊢≡ · equality-subject-typing ⊢≡₁
  equality-subject-typing (suc-cong ⊢≡) = suc (equality-subject-typing ⊢≡)

  -- Equality preserves typing.

  equality-preserves-typing : Γ ⊢ t ≡ t₁ ∷ A → Γ ⊢ t₁ ∷ A
  equality-preserves-typing (refl ⊢t) = ⊢t
  equality-preserves-typing (sym ⊢≡) = equality-subject-typing ⊢≡
  equality-preserves-typing (trans ⊢≡ ⊢≡₁) = equality-preserves-typing ⊢≡₁
  equality-preserves-typing (β-red ⊢t ⊢t₁) = 
    substitution-preserves-typing (sgSubstₜ ⊢t₁) ⊢t
  equality-preserves-typing (ρ-equal ⊢t ⊢t₁ ⊢≡) = ⊢t₁
  equality-preserves-typing (·-cong ⊢≡ ⊢≡₁) = 
    equality-preserves-typing ⊢≡ · equality-preserves-typing ⊢≡₁
  equality-preserves-typing (suc-cong ⊢≡) = suc (equality-preserves-typing ⊢≡)

-- Term of reduction is well typed.

reduction-subject-typing : Γ ⊢ t ⇒ t′ ∷ A → Γ ⊢ t ∷ A
reduction-subject-typing = equality-subject-typing ∘ equality-subsumes-reduction

-- Reduction preserves typing.

reduction-preserves-typing : Γ ⊢ t ⇒ t′ ∷ A → Γ ⊢ t′ ∷ A
reduction-preserves-typing = equality-preserves-typing ∘ equality-subsumes-reduction

-- Weak Head Normalization Theorem: all well-typed terms can be reduced to 
-- whnf.

whn : Γ ⊢ t ∷ A → ∃ λ t′ → Whnf t′ × Γ ⊢ t ⇒* t′ ∷ A
whn = ?
