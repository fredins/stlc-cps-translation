
module Stlc.LogicalRelation where

-- Kripke logical relation Γ ⊩ t : A and Γ ⊩ t ≡ t′ : A. Kripke Worlds are 
-- contexts and the Kripke relation is context extension (weakening).
-- We want to model judgmental typing (Γ ⊢ t : A) and equality (Γ ⊢ t ≡ t′ : A).

--         Fundamental theorem
--  +-------------------------------------+
--  |                                     ↓
--  Γ ⊢ J ←------------- Γ ⊩ J ←--------- Γ ⊩ᵛ J
--         Well-formness        Soundness


open import Data.Nat
open import Data.Product using (∃; _×_)

open import Stlc.Untyped
open import Stlc.Typed

private variable
  m n        : ℕ
  A B        : Type
  t t′ t″ t₁ : Term _
  Γ          : Con _

-- Reducible equality.

data _⊩_≡_∷_ : Con n → Term n → Term n → Type → Set where

-- Valid equality.

data _⊩ᵛ_≡_∷_ : Con n → Term n → Term n → Type → Set where


-- 𝕤𝕟⟨_∷_⟩ 
data _∷_∈𝕤𝕟 : Term n → Type → Set where


well-formness : Γ ⊩ t ≡ t′ ∷ A → Γ ⊢ t ≡ t′ ∷ A
well-formness = ?

soundness : Γ ⊩ᵛ t ≡ t′ ∷ A → Γ ⊢ t ≡ t′ ∷ A
soundness = ?

fundamental-theorem : Γ ⊢ t ≡ t′ ∷ A → Γ ⊩ᵛ t ≡ t′ ∷ A
fundamental-theorem = ?

