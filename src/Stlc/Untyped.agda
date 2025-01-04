
module Stlc.Untyped where

open import Data.Nat using (ℕ; zero; suc; 2+)
open import Data.Fin using (Fin; zero; suc; #_)

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
  i : ∀ {m} → Wk m m
  ↑_       : ∀ {m n} → Wk m n → Wk (suc m) n
  ⇑_       : ∀ {m n} → Wk m n → Wk (suc m) (suc n)

infixl 5 _∙_ 

_∙_ : ∀ {l m n} (η : Wk l m) (η₁ : Wk m n) → Wk l n
i     ∙ η₁     = η₁
(↑ η) ∙ η₁     = ↑ (η ∙ η₁)
(⇑ η) ∙ i      = ⇑ η
(⇑ η) ∙ (↑ η₁) = ↑ (η ∙ η₁)
(⇑ η) ∙ (⇑ η₁) = ⇑ (η ∙ η₁)

wkVar : {m n : ℕ} (η : Wk m n) (x : Fin n) → Fin m
wkVar i     x       = x
wkVar (↑ η) x       = suc (wkVar η x)
wkVar (⇑ η) zero    = zero
wkVar (⇑ η) (suc x) = suc (wkVar η x)

wk : ∀ {m n} (η : Wk m n) (t : Term n) → Term m
wk η (var x)  = var (wkVar η x)
wk η (lam t)  = lam (wk (⇑ η) t)
wk η (t · t₁) = wk η t · wk η t₁
wk η zero     = zero
wk η (suc t)  = suc (wk η t)

wk1 : ∀ {m} → Term m → Term (suc m)
wk1 = wk (↑ i)

wk2 : ∀ {m} → Term m → Term (2+ m)
wk2 = wk (↑ ↑ i)

--------------------------------------------------------------------------------
-- * Substitution 

Subst : ℕ → ℕ → Set
Subst m n = Fin n → Term m

_↑ : ∀ {m n} (σ : Subst m n) → Subst (suc m) n
(σ ↑) x = wk (↑ i) (σ x)

_⇑ : ∀ {m n} (σ : Subst m n) → Subst (suc m) (suc n)
(σ ⇑) zero    = var zero
(σ ⇑) (suc x) = (σ ↑) x

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
consSubst σ t (suc x ) = σ x

sgSubst : ∀ {m} → Term m → Subst m (suc m)
sgSubst = consSubst idSubst

_[_]₀ : ∀ {m} → Term (suc m) → Term m → Term m
t [ t₁ ]₀ = t [ sgSubst t₁ ]

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
