
module Stlc.CpsTransformation where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc; #_)

open import Stlc.Untyped
open import Stlc.Typed

private variable
  n : ℕ

postulate
  ⊥ : Type

¬_ : Type → Type
¬ A = A ⟶ ⊥

cpst⟦_⟧ : Type → Type
cpst⟦ A ⟶ B ⟧ = ¬ (¬ cpst⟦ A ⟧ ⟶ ¬ cpst⟦ B ⟧)
cpst⟦ N ⟧ = ¬ N

cps⟦_⟧ : Term n → Term n
cps⟦ var x  ⟧  = lam (var (# 0) · wk1 (var x))
cps⟦ lam t  ⟧  = lam (var (# 0) · lam (wk1 cps⟦ t ⟧))
cps⟦ t · t₁ ⟧  = lam (wk1 cps⟦ t ⟧ · lam (wk2 cps⟦ t₁ ⟧ · lam (var (# 1) · var (# 0) · var (# 2))))
cps⟦ zero   ⟧  = lam (var (# 0) · zero)
cps⟦ suc t  ⟧  = lam (wk1 cps⟦ t ⟧ · lam (suc (var (# 0))))

