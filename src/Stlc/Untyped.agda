
module Stlc.Untyped where

open import Data.Nat using (ℕ; zero; suc; 2+)
open import Data.Fin using (Fin; zero; suc; #_)
import Relation.Binary.PropositionalEquality as PE
open PE.≡-Reasoning

infixr 5 _⟶_ 
infixl 5 _·_ 

data Type : Set where
  _⟶_ : Type → Type → Type
  N   : Type
--  ⊥   : Type

data Term (n : ℕ) : Set where
  var  : (x : Fin n) → Term n
  lam  : Term (suc n) → Term n
  _·_  : Term n → Term n → Term n
  zero : Term n
  suc  : Term n → Term n

private variable
  t t₁ : Term _

--------------------------------------------------------------------------------
-- * Weakening

data Wk : ℕ → ℕ → Set where
  id : ∀ {m} → Wk m m
  ↑_ : ∀ {m n} → Wk m n → Wk (suc m) n
  ⇑_ : ∀ {m n} → Wk m n → Wk (suc m) (suc n)

infixl 5 _∙_ 

_∙_ : ∀ {l m n} (ρ : Wk l m) (ρ₁ : Wk m n) → Wk l n
id    ∙ ρ₁     = ρ₁
(↑ ρ) ∙ ρ₁     = ↑ (ρ ∙ ρ₁)
(⇑ ρ) ∙ id     = ⇑ ρ
(⇑ ρ) ∙ (↑ ρ₁) = ↑ (ρ ∙ ρ₁)
(⇑ ρ) ∙ (⇑ ρ₁) = ⇑ (ρ ∙ ρ₁)

wkVar : {m n : ℕ} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id    x       = x
wkVar (↑ ρ) x       = suc (wkVar ρ x)
wkVar (⇑ ρ) zero    = zero
wkVar (⇑ ρ) (suc x) = suc (wkVar ρ x)

wk : ∀ {m n} (ρ : Wk m n) (t : Term n) → Term m
wk ρ (var x)  = var (wkVar ρ x)
wk ρ (lam t)  = lam (wk (⇑ ρ) t)
wk ρ (t · t₁) = wk ρ t · wk ρ t₁
wk ρ zero     = zero
wk ρ (suc t)  = suc (wk ρ t)

wk1 : ∀ {m} → Term m → Term (suc m)
wk1 = wk (↑ id)

wk2 : ∀ {m} → Term m → Term (2+ m)
wk2 = wk (↑ ↑ id)

--------------------------------------------------------------------------------
-- * Substitution 

Subst : ℕ → ℕ → Set
Subst m n = Fin n → Term m

_↑ : ∀ {m n} (σ : Subst m n) → Subst (suc m) n
(σ ↑) x = wk1 (σ x)

_⇑ : ∀ {m n} (σ : Subst m n) → Subst (suc m) (suc n)
(σ ⇑) zero    = var zero
(σ ⇑) (suc x) = wk1 (σ x)

_[_] : ∀ {m n} (t : Term n) (σ : Subst m n) → Term m
var x    [ σ ] = σ x
lam t    [ σ ] = lam (t [ σ ⇑ ])
(t · t₁) [ σ ] = t [ σ ] · t₁ [ σ ]
zero     [ σ ] = zero
suc t    [ σ ] = suc (t [ σ ])

idSubst : ∀ {m} → Subst m m
idSubst = var

consSubst : ∀ {m n} → Subst m n → Term m → Subst m (suc n)
consSubst σ t zero    = t
consSubst σ t (suc x) = σ x

sgSubst : ∀ {m} → Term m → Subst m (suc m)
sgSubst = consSubst idSubst

_[_]₀ : ∀ {m} → Term (suc m) → Term m → Term m
t [ t₁ ]₀ = t [ sgSubst t₁ ]

head : ∀ {m n} → Subst m (suc n) → Term m
head σ = σ zero

tail : ∀ {m n} → Subst m (suc n) → Subst m n
tail σ x = σ (suc x)

--------------------------------------------------------------------------------
-- * Contexts 

infixl 5 _▹_

data Con : ℕ → Set where
  ε   : Con 0         
  _▹_ : {n : ℕ} → Con n → Type → Con (suc n)   

--------------------------------------------------------------------------------
-- * Neutral and normal terms

mutual
  data Ne {n} : Term n → Set where
    var : (x : Fin n) → Ne (var x)
    app : Ne t → Ne (t · t₁)

  data Whnf {n} : Term n → Set where
    ne   : Ne t → Whnf t
    lam  : Whnf (lam t)
    zero : Whnf zero
    suc  : Whnf (suc t)
