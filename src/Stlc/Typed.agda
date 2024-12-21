
module Stlc.Typed where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
  using (Star)
  renaming (ε to []; _◅_ to _∷_)
import Relation.Binary.PropositionalEquality as PE
open import Data.Product using (_×_; _,_)

open import Stlc.Untyped

private variable
  m n  : ℕ
  A B  : Type
  t t′ t₁ t₁′  : Term _
  Γ    : Con _
  x    : Fin _

infix 4 _∷_∈_ _⊢_∷_ _⊢_⇒_∷_

-- Well-formed variable
data _∷_∈_ : (x : Fin n) (A : Type) (Γ : Con n) → Set where
  here  : zero ∷ A ∈ Γ ▹ A
  there : x ∷ A ∈ Γ → suc x ∷ A ∈ Γ ▹ B

-- Well-formed term of a type
data _⊢_∷_ (Γ : Con n) : Term n → Type → Set where
  var : 
    x ∷ A ∈ Γ → 
    -------------
    Γ ⊢ var x ∷ A

  lam : 
    Γ ▹ A ⊢ t ∷ B →
    -----------------
    Γ ⊢ lam t ∷ A ⟶ B

  _·_ :
    Γ ⊢ t ∷ A ⟶ B →
    Γ ⊢ t₁ ∷ A →
    ---------------
    Γ ⊢ t · t₁ ∷ B

  zero : 
    ------------
    Γ ⊢ zero ∷ N

  suc :
    Γ ⊢ t ∷ N →
    -------------
    Γ ⊢ suc t ∷ N


data _⊢_⇒_∷_ (Γ : Con n) : Term n → Term n → Type → Set where
  β-lam : 
    Γ ▹ A ⊢ t ∷ B →
    Γ ⊢ t₁ ∷ A → 
    ------------------------------
    Γ ⊢ lam t · t₁ ⇒ t [ t₁ ]₀ ∷ B

  ξ-lam :
    Γ ▹ A ⊢ t ⇒ t′ ∷ B →
    ----------------------
    Γ ⊢ lam t ⇒ lam t′ ∷ B

  ξ-·ₗ :
    Neutral t → -- fel ?
    Γ ⊢ t ⇒ t′ ∷ A →
    ------------------------
    Γ ⊢ t · t₁ ⇒ t′ · t₁ ∷ A

  ξ-·ᵣ :
    Normal t →
    Γ ⊢ t₁ ⇒ t₁′ ∷ A →
    ------------------------
    Γ ⊢ t · t₁ ⇒ t · t₁′ ∷ A

  ξ-suc :
    Γ ⊢ t ⇒ t′ ∷ N →
    ----------------------
    Γ ⊢ suc t ⇒ suc t′ ∷ N

_⊢_⇒*_∷_ : Con n → Term n → Term n → Type → Set
Γ ⊢ t ⇒* t′ ∷ A = Star (λ t t′ → Γ ⊢ t ⇒ t′ ∷ A) t t′

_⊢_↘_∷_ : Con n → Term n → Term n → Type → Set
Γ ⊢ t ↘ t′ ∷ A = (Γ ⊢ t ⇒* t′ ∷ A) × Normal t′



