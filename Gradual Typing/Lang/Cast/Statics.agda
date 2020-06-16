module Lang.Cast.Statics where

open import Type
open import Variable
open import BlameLabel

data Cast : Type → Type → Set where
  _⟹[_]_ : (S : Type)(l : BlameLabel)(T : Type) → Cast S T

infix  3 _⊢_

data _⊢_ : Context → Type → Set where

  lit : ∀ {Γ B}
    → (v : BaseValue B)
    → Γ ⊢ (` (′ B))
                      
  var : ∀ {Γ T}
    → (x : Γ ∋ T)
    --------
    → Γ ⊢ T

  fun : ∀ {Γ} S T
    → (e : Γ , S ⊢ T)
    -------------
    → Γ ⊢ ` S ⇒ T
  
  app : ∀ {Γ S T}
    → (e1 : Γ ⊢ ` S ⇒ T)
    → (e2 : Γ ⊢ S)
    --------
    → Γ ⊢ T

  inj₁ : ∀ {Γ T₁ T₂}
    → Γ ⊢ T₁
    --------
    → Γ ⊢ ` T₁ ⊕ T₂

  inj₂ : ∀ {Γ T₁ T₂}
    → Γ ⊢ T₂
    --------
    → Γ ⊢ ` T₁ ⊕ T₂

  which : ∀ {Γ T₁ T₂ T}
    → Γ ⊢ ` T₁ ⊕ T₂
    → Γ , T₁ ⊢ T
    → Γ , T₂ ⊢ T
    --------
    → Γ ⊢ T

  cons : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ T1)
    → (e2 : Γ ⊢ T2)
    -----
    → Γ ⊢ (` T1 ⊗ T2)

  car : ∀ {Γ S T}
    → (e : Γ ⊢ (` S ⊗ T))
    → Γ ⊢ S
    
  cdr : ∀ {Γ S T}
    → (e : Γ ⊢ (` S ⊗ T))
    → Γ ⊢ T
  
  _⟨_⟩ : ∀ {Γ T S}
    → (e : Γ ⊢ S)
    → (c : Cast S T)
    --------
    → Γ ⊢ T
