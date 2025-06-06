
module Stlc.CpsTransformation where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Product using (∃; ∃₂; ∃-syntax; Σ-syntax; _×_; _,_; -,_)
import Relation.Binary.PropositionalEquality as PE
open PE.≡-Reasoning

open import Stlc.Untyped
open import Stlc.Typed

private variable
  m n : ℕ
  t t₁ k : Term _
  Γ Δ : Con _
  A B C D : Type
  x : Fin _

postulate
  ⊥ : Type

¬_ : Type → Type
¬ A = A ⟶ ⊥


infix 4 ⊢_↝_ _⊢_∷_↝÷_∷_ _⊢_∷_↝+_∷_ _⊢_∷_¦_↝★_ ⊢_↝÷_ ⊢_↝+_


-- TODO: should probably define two languages like Cong 
-- (but maybe my current knowledge will be enough to perform the untyped Haskell version)


-- CPS translation of types

mutual

  data ⊢_↝÷_ : Type → Type → Set where
    ¬¬_ : 
      ⊢ A ↝+ B → 
      ------------------
      ⊢ A ↝÷ (B ⟶ ⊥) ⟶ ⊥

  data ⊢_↝+_ : Type → Type → Set where
    N : 
      --------
      ⊢ N ↝+ N
    _⟶_ :
      
      ⊢ A ↝÷ C →
      ⊢ B ↝+ D →
      ------------
      ⊢ A ⟶ B ↝+ C ⟶ D


-- CPS translation of typing contexts

data ⊢_↝_ : ∀ {n} → Con n → Con n → Set where
  ε : 
    -------
    ⊢ ε ↝ ε 

  _▹_ : 
    ⊢ Γ ↝ Δ → 
    ⊢ A ↝÷ B →
    ---------------
    ⊢ Γ ▹ A ↝ Δ ▹ B


-- CPS translation of terms including a colon translation

mutual 

  data _⊢_∷_↝÷_∷_ (Γ : Con n) : Term n → Type → Term n → Type → Set where
    cps : 
      ⊢ A ↝+ B →
      Γ ▹ (B ⟶ ⊥) ⊢ wk1 t ∷ A ¦ var zero ↝★ t₁ →
      --------------------------------------
      Γ ⊢ t ∷ A ↝÷ lam t₁ ∷ (B ⟶ ⊥) ⟶ ⊥

  data _⊢_∷_↝+_∷_ (Γ : Con n) : Term n → Term n → Set where
  {-
    lam :
      Γ ▹ A ⊢ t ∷ B → -- don't like this
      Γ ▹ A ⊢ t ↝÷ t₁ →
      -------------------
      Γ ⊢ lam t ↝+ lam t₁
  -}


  data _⊢_∷_¦_↝★_ (Γ : Con n) : Term n → Type → Term n → Term n → Set where
    var : 
      --------------------------
      Γ ⊢ var x ∷ A ¦ k ↝★ var x · k

  {-
    lam : 
      --------------------------
      Γ ⊢ lam t ∷ A ¦ k ↝★ k · lam t
  -}

    -- Figure out evaluation order
    {-
    ·zero : Γ ⊢ t · zero ¦ k ↝★ ?
    ·lam : Γ ⊢ t · lam t₁ ¦ k ↝★ ?
    -}

    zero : 
      ------------------------
      Γ ⊢ zero ∷ N ¦ k ↝★ k · zero



CPS : Γ ⊢ t ∷ A → ∃₂ λ t₁ B → Γ ⊢ t ∷ A ↝÷ t₁ ∷ B
CPS (var x) = {! !}
CPS (lam t) = {! !}
CPS (t · t₁) = {! !}
CPS zero = lam (var (# 0) · zero) , (N ⟶ ⊥) ⟶ ⊥ , cps N zero
CPS (suc t) = {! !}


_ : Γ ⊢ zero ∷ N ↝÷ lam (var (# 0) · zero) ∷ (N ⟶ ⊥) ⟶ ⊥
_ = cps N zero

-- type-preserving : Γ ⊢ t ∷ A → Γ ⊢ t ∷ A ↝÷ (



  {-
  colon  : {t k : Term n} (Γ : Con n) → Γ ⊢ t ∷ A → Γ ⊢ k ∷ B ⟶ ⊥ → Σ[ Δ ∈ Con n ] Σ[ t₁ ∈ Term n ] Γ ⊢ t₁ ∷ ⊥
  colon Γ (var here) k = {! !} , {! !} , {! !} · {! !}
  colon Γ (var (there x)) k = {! !}


  colon Γ (lam t) k = {! !}
  colon Γ (t · t₁) k = {! !}
  colon Γ zero k = {! !}
  colon Γ (suc t) k = {! !}
  -}


{-
data IsValue {n : ℕ} : Term n → Set where
  var  : (x : Fin n) → IsValue (var x)
  lam  : (t : Term (suc n)) → IsValue (lam t)
  zero : IsValue zero

data IsComputation {n : ℕ} : Term n → Set where
  suc : (t : Term n) → IsComputation (suc t)
  _·_ : (t t₁ : Term n) → IsComputation (t · t₁)


-- infix 5 _¦ᵛ_ _¦ᶜ_ 

mutual 
  infix 5 _¦_ 

  _¦_ : Term n → Term n → Term n
  var x    ¦ k = var x · k
  lam t    ¦ k = k · cps (lam t)
  (t · t₁) ¦ k = {! !}
  zero     ¦ k = k · zero
  suc t    ¦ k = {! !}

  cps : Term n → Term n
  cps (var x)  = var x
  cps (lam t)  = lam (cps t)
  cps (t · t₁) = lam (wk1 (t · t₁) ¦ var zero)
  cps zero     = zero
  cps (suc t)  = lam (suc (wk1 t) ¦ var zero)

-}



-- _¦ᵛ_ : {n : ℕ} {t : Term n} → IsValue t → Term n → Term n

{-
var x ¦ᵛ k = {! !}
lam t ¦ᵛ k = {! !}
zero  ¦ᵛ k = {! !}

suc t    ¦ᶜ k = {! !}
(t · t₁) ¦ᶜ k = {! !}

-}


{-
cps : Term n → Term n
_¦_ : Term n → Term n → Term n 

infix 5 _¦_

var x    ¦ k = k · var x
lam t    ¦ k = k · lam (cps t)
(t · t₁) ¦ k = {! !}
zero     ¦ k = k · zero
suc t    ¦ k = t ¦ lam (suc (var (# 0)) · wk1 k)

{-# TERMINATING #-}
cps (var x)  = var x
cps (lam t)  = lam (cps t)
cps (t · t₁) = {! !}
cps zero     = zero
cps (suc t)  = lam (suc (wk1 t) ¦ var (# 0))
-}






-- ex : Term 1
-- ex = suc (var zero)
-- cps (suc t) = λ k → (λ y → suc y k) · t
-- _- _ : cps (suc (var (zero {n = 1}))) PE.≡ lam (lam (suc (var zero) · var (suc zero)) · var (suc zero))
-- _ = PE.refl
-- _ : cps (lam (var (# 0) · var (# 0))) PE.≡ lam (var (# 0) · lam (lam (var (# 1) · var (# 1) · var (# 0))))
-- _ = PE.refl

{-
cpst⟦_⟧ : Type → Type
cpst⟦ A ⟶ B ⟧ = ¬ (¬ cpst⟦ A ⟧ ⟶ ¬ cpst⟦ B ⟧)
cpst⟦ N ⟧ = ¬ N

cps⟦_⟧ : Term n → Term n
cps⟦ var x  ⟧  = lam (var (# 0) · wk1 (var x))
cps⟦ lam t  ⟧  = lam (var (# 0) · lam (wk1 cps⟦ t ⟧))
cps⟦ t · t₁ ⟧  = lam (wk1 cps⟦ t ⟧ · lam (wk2 cps⟦ t₁ ⟧ · lam (var (# 1) · var (# 0) · var (# 2))))
cps⟦ zero   ⟧  = lam (var (# 0) · zero)
cps⟦ suc t  ⟧  = lam (wk1 cps⟦ t ⟧ · lam (suc (var (# 0))))

ex : Term 0
ex = lam (var (# 0) · var (# 0))

_ : cps⟦ ex ⟧ PE.≡ 
  lam
  (var zero ·
   lam
   (lam
    (lam (var zero · var (suc (suc (suc zero)))) ·
     lam
     (lam (var zero · var (suc (suc (suc (suc zero))))) ·
      lam (var (suc zero) · var zero · var (suc (suc zero)))))))
_ = PE.refl
-}
