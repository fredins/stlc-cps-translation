
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

open import Stlc.Untyped
open import Stlc.Typed

private variable
  n       : ℕ
  A B     : Type
  t t′ t″ : Term _
  Γ       : Con _

-- Neutral term do not reduce.

ne-reduction : Γ ⊢ t ⇒ t′ ∷ A → ¬ (Ne t)
ne-reduction (β-red x x₂) (app ())
ne-reduction (·-cong x x₂) (app x₁) = ne-reduction x x₁

-- WHNFs do not reduce.

whnf-reduction : Γ ⊢ t ⇒ t′ ∷ A → ¬ (Whnf t)
whnf-reduction (β-red x x₂) (ne (app ()))
whnf-reduction (·-cong x x₂) (ne (app x₁)) = whnf-reduction x (ne x₁)

-- Reduction is deterministic.

det-reduction : {Γ : Con n} → Γ ⊢ t ⇒ t′ ∷ A → Γ ⊢ t ⇒ t″ ∷ B → t′ PE.≡ t″
det-reduction (β-red x x₂) (β-red x₁ x₃) = PE.refl
det-reduction (·-cong x x₂) (·-cong x₁ x₃) = PE.cong (_· _) (det-reduction x x₁)

-- Reduction to WHNF is deterministic.

det-reduction-↘whnf : Γ ⊢ t ↘ t′ ∷ A → Γ ⊢ t ↘ t″ ∷ B → t′ PE.≡ t″
det-reduction-↘whnf ([] , w) ([] , w₁) = PE.refl
det-reduction-↘whnf ([] , w) (x₁ ∷ xs₁ , w₁) = ⊥-elim (whnf-reduction x₁ w)
det-reduction-↘whnf (x ∷ xs , w) ([] , w₁) = ⊥-elim (whnf-reduction x w₁)
det-reduction-↘whnf (x ∷ xs , w) (x₁ ∷ xs₁ , w₁) = 
  det-reduction-↘whnf (xs , w) (PE.subst (_ ⊢_↘ _ ∷ _) (det-reduction x₁ x) (xs₁ , w₁)) 
