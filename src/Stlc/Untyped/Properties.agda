
module Stlc.Untyped.Properties where

open import Data.Nat using (ℕ; zero; suc; 2+)
open import Data.Fin using (Fin; zero; suc; #_)
import Relation.Binary.PropositionalEquality as PE
open PE.≡-Reasoning

open import Stlc.Untyped

private variable
  l m n  : ℕ
  x    : Fin _
  t t₁ : Term _
  ρ ρ₁ : Wk _ _
  σ σ₁ : Subst _ _

-- Weakening properties.

wkVar-id : wkVar id x PE.≡ x
wkVar-id = PE.refl

wkVar-⇑ : 
  (∀ x → wkVar ρ x PE.≡ wkVar ρ₁ x) →
  ∀ x → wkVar (⇑ ρ) x PE.≡ wkVar (⇑ ρ₁) x
wkVar-⇑ f zero = PE.refl
wkVar-⇑ f (suc x) = PE.cong suc (f x)

wkVar-⇑-id : (x : Fin (suc n)) → wkVar (⇑ id) x PE.≡ wkVar id x
wkVar-⇑-id zero = PE.refl
wkVar-⇑-id (suc x) = PE.refl

wkVar-to-wk : 
  (∀ x → wkVar ρ x PE.≡ wkVar ρ₁ x) →
  (t : Term n) → 
  wk ρ t PE.≡ wk ρ₁ t
wkVar-to-wk f (var x) = PE.cong var (f x)
wkVar-to-wk f (lam t) = PE.cong lam (wkVar-to-wk (wkVar-⇑ f) t)
wkVar-to-wk f (t · t₁) = PE.cong₂ _·_ (wkVar-to-wk f t) (wkVar-to-wk f t₁)
wkVar-to-wk f zero = PE.refl
wkVar-to-wk f (suc t) = PE.cong suc (wkVar-to-wk f t)

wk-id : ∀ {n} (t : Term n) → wk id t PE.≡ t
wk-id (var x) = PE.refl
wk-id (lam t) = PE.cong lam (PE.trans (wkVar-to-wk wkVar-⇑-id t) (wk-id t))
wk-id (t · t₁) = PE.cong₂ _·_ (wk-id t) (wk-id t₁)
wk-id zero = PE.refl
wk-id (suc t) = PE.cong suc (wk-id t)

wkVar-comp : ∀ (ρ : Wk l m) (ρ₁ : Wk m n) x → wkVar ρ (wkVar ρ₁ x) PE.≡ wkVar (ρ ∙ ρ₁) x
wkVar-comp id ρ₁ x = PE.refl
wkVar-comp (↑ ρ) ρ₁ x = PE.cong suc (wkVar-comp ρ ρ₁ x)
wkVar-comp (⇑ ρ) id x = PE.refl
wkVar-comp (⇑ ρ) (↑ ρ₁) x = PE.cong suc (wkVar-comp ρ ρ₁ x)
wkVar-comp (⇑ ρ) (⇑ ρ₁) zero = PE.refl
wkVar-comp (⇑ ρ) (⇑ ρ₁) (suc x) = PE.cong suc (wkVar-comp ρ ρ₁ x)

wk-comp : ∀ (ρ : Wk l m) (ρ₁ : Wk m n) t → wk ρ (wk ρ₁ t) PE.≡ wk (ρ ∙ ρ₁) t
wk-comp ρ ρ₁ (var x) = PE.cong var (wkVar-comp ρ ρ₁ x)
wk-comp ρ ρ₁ (lam t) = PE.cong lam (wk-comp (⇑ ρ) (⇑ ρ₁) t)
wk-comp ρ ρ₁ (t · t₁) = PE.cong₂ _·_ (wk-comp ρ ρ₁ t) (wk-comp ρ ρ₁ t₁)
wk-comp ρ ρ₁ zero = PE.refl
wk-comp ρ ρ₁ (suc t) = PE.cong suc (wk-comp ρ ρ₁ t)

-- Substituition properties.

substVar-⇑ :
  (∀ x → σ x PE.≡ σ₁ x) →
  (x : Fin (suc n)) →
  (σ ⇑) x PE.≡ (σ₁ ⇑) x
substVar-⇑ f zero = PE.refl
substVar-⇑ f (suc x) = PE.cong wk1 (f x)

substVar-to-subst : 
  (∀ x → σ x PE.≡ σ₁ x) →
  (t : Term n) → 
  t [ σ ] PE.≡ t [ σ₁ ]
substVar-to-subst f (var x) = f x
substVar-to-subst f (lam t) = PE.cong lam (substVar-to-subst (substVar-⇑ f) t)
substVar-to-subst f (t · t₁) = PE.cong₂ _·_ (substVar-to-subst f t) (substVar-to-subst f t₁)
substVar-to-subst f zero = PE.refl
substVar-to-subst f (suc t) = PE.cong suc (substVar-to-subst f t)
