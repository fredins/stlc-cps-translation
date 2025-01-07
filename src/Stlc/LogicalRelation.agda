
module Stlc.LogicalRelation where

-- Kripke logical relation Γ ⊩ t : A and Γ ⊩ t ≡ t′ : A. Kripke Worlds are 
-- contexts and the Kripke relation is context extension (weakening).

-- We want to model typing and equality, so we

open import Data.Nat
open import Data.Product using (∃; _×_)

open import Stlc.Untyped
open import Stlc.Typed

private variable
  m n        : ℕ
  A B        : Type
  t t′ t″ t₁ : Term _
  Γ          : Con _


