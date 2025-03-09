
module Stlc.Typed where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
  using (ε; Star)
  renaming (_◅_ to _◃_)
import Relation.Binary.PropositionalEquality as PE
open import Data.Product using (_×_; _,_)

open import Stlc.Untyped

private variable
  m n            : ℕ
  A B C          : Type
  t t′ t″ t₁ t₁′ : Term _
  Γ Δ Δ₁         : Con _
  x              : Fin _
  ρ ρ₁           : Wk _ _
  σ σ₁           : Subst _ _

infix 4 _∷_∈_ _⊢_∷_ _⊢_⇒_∷_ _⊢_≡_∷_

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

-- Term equality

data _⊢_≡_∷_ (Γ : Con n) : Term n → Term n → Type → Set where
  refl : 
    Γ ⊢ t ∷ A →
    -------------
    Γ ⊢ t ≡ t ∷ A

  sym : 
    Γ ⊢ t ≡ t′ ∷ A →
    ----------------
    Γ ⊢ t′ ≡ t ∷ A

  trans :
    Γ ⊢ t ≡ t′ ∷ A → 
    Γ ⊢ t′ ≡ t″ ∷ A →
    -----------------
    Γ ⊢ t ≡ t″ ∷ A

  β-red :
    Γ ▹ A ⊢ t ∷ B →
    Γ ⊢ t₁ ∷ A →
    ------------------------------
    Γ ⊢ lam t · t₁ ≡ t [ t₁ ]₀ ∷ B

  ρ-equal :
    Γ ⊢ t ∷ A ⟶ B →
    Γ ⊢ t₁ ∷ A ⟶ B →
    Γ ▹ A ⊢ wk1 t · var zero ≡ wk1 t₁ · var zero ∷ B →
    --------------------------------------------------
    Γ ⊢ t ≡ t₁ ∷ A ⟶ B

  ·-cong :
    Γ ⊢ t ≡ t′ ∷ A ⟶ B →
    Γ ⊢ t₁ ≡ t₁′ ∷ A →
    -------------------------
    Γ ⊢ t · t₁ ≡ t′ · t₁′ ∷ B

  suc-cong :
    Γ ⊢ t ≡ t′ ∷ N →
    ----------------------
    Γ ⊢ suc t ≡ suc t′ ∷ N
     
-- Reduction to WHNF

data _⊢_⇒_∷_ (Γ : Con n) : Term n → Term n → Type → Set where
  β-red : 
    Γ ▹ A ⊢ t ∷ B →
    Γ ⊢ t₁ ∷ A → 
    ------------------------------
    Γ ⊢ lam t · t₁ ⇒ t [ t₁ ]₀ ∷ B

  ·-cong :
    Γ ⊢ t ⇒ t′ ∷ A ⟶ B →
    Γ ⊢ t₁ ∷ A →
    ------------------------
    Γ ⊢ t · t₁ ⇒ t′ · t₁ ∷ B

-- Reduction closure.

_⊢_⇒*_∷_ : Con n → Term n → Term n → Type → Set
Γ ⊢ t ⇒* t′ ∷ A = Star (λ t t′ → Γ ⊢ t ⇒ t′ ∷ A) t t′

-- Reduction to WHNF.

_⊢_↘_∷_ : Con n → Term n → Term n → Type → Set
Γ ⊢ t ↘ t′ ∷ A = (Γ ⊢ t ⇒* t′ ∷ A) × Whnf t′

-- Well-formed weakening.

infix 4 _∷_≤_ _⊢ˢ_∷_

data _∷_≤_ : Wk m n → Con m → Con n → Set where
  id : id ∷ Γ ≤ Γ
  ↑_ : ρ ∷ Δ ≤ Γ → ↑ ρ ∷ Δ ▹ A ≤ Γ
  ⇑_ : ρ ∷ Δ ≤ Γ → ⇑ ρ ∷ Δ ▹ A ≤ Γ ▹ A
  
infixl 5 _∙ₜ_ 

_∙ₜ_ : ρ ∷ Δ₁ ≤ Δ → ρ₁ ∷ Δ ≤ Γ → ρ ∙ ρ₁ ∷ Δ₁ ≤ Γ
id ∙ₜ η₁ = η₁
↑ η ∙ₜ η₁ = ↑ (η ∙ₜ η₁)
⇑ η ∙ₜ id = ⇑ η
⇑ η ∙ₜ (↑ η₁) = ↑ (η ∙ₜ η₁)
⇑ η ∙ₜ (⇑ η₁) = ⇑ (η ∙ₜ η₁)

wkVarₜ : ρ ∷ Δ ≤ Γ → x ∷ A ∈ Γ → wkVar ρ x ∷ A ∈ Δ
wkVarₜ id x∈ = x∈
wkVarₜ (↑ η) x∈ = there (wkVarₜ η x∈)
wkVarₜ (⇑ η) here = here
wkVarₜ (⇑ η) (there x∈) = there (wkVarₜ η x∈)

wkₜ : ρ ∷ Δ ≤ Γ → Γ ⊢ t ∷ A → Δ ⊢ wk ρ t ∷ A
wkₜ η (var x∈) = var (wkVarₜ η x∈)
wkₜ η (lam ⊢t) = lam (wkₜ (⇑ η) ⊢t)
wkₜ η (⊢t · ⊢t₁) = wkₜ η ⊢t · wkₜ η ⊢t₁
wkₜ η zero = zero
wkₜ η (suc ⊢t) = suc (wkₜ η ⊢t)

wk1ₜ : Γ ⊢ t ∷ A → Γ ▹ B ⊢ wk1 t ∷ A
wk1ₜ = wkₜ (↑ id)

-- Well-formed substitution.

infixl 5 _▹_

data _⊢ˢ_∷_ (Δ : Con m) : Subst m n → Con n → Set where
  ε   : Δ ⊢ˢ σ ∷ ε 
  _▹_ : Δ ⊢ˢ tail σ ∷ Γ → 
        Δ ⊢ head σ ∷ A →
        Δ ⊢ˢ σ ∷ Γ ▹ A

_↑ₜ :  Δ ⊢ˢ σ ∷ Γ → Δ ▹ A ⊢ˢ σ ↑ ∷ Γ
ε ↑ₜ = ε
(⊢σ ▹ x) ↑ₜ = ⊢σ ↑ₜ ▹ wk1ₜ x

_⇑ₜ : Δ ⊢ˢ σ ∷ Γ → Δ ▹ A ⊢ˢ σ ⇑ ∷ Γ ▹ A 
_⇑ₜ ⊢σ = ⊢σ ↑ₜ ▹ var here
  
idSubstₜ : Γ ⊢ˢ idSubst ∷ Γ
idSubstₜ {Γ = ε} = ε
idSubstₜ {Γ = Γ ▹ A} = idSubstₜ ↑ₜ ▹ var here

consSubstₜ : Δ ⊢ˢ σ ∷ Γ → Δ ⊢ t ∷ A → Δ ⊢ˢ consSubst σ t ∷ Γ ▹ A
consSubstₜ = _▹_

sgSubstₜ : Γ ⊢ t ∷ A → Γ ⊢ˢ sgSubst t ∷ Γ ▹ A
sgSubstₜ = consSubstₜ idSubstₜ
