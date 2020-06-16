module Variable where

open import Type

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infix  3 _∋_
infixr 4 _,_

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  zero : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  suc  : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

∋→ℕ : ∀ {Γ T} → Γ ∋ T → ℕ
∋→ℕ zero = zero
∋→ℕ (suc x) = suc (∋→ℕ x)

inv-suc : {m n : ℕ} → (eq : _≡_ {A = ℕ} (suc m) (suc n)) → m ≡ n
inv-suc refl = refl

inv-∋→ℕ : ∀ {Γ T₁ T₂} → (x₁ : Γ ∋ T₁)(x₂ : Γ ∋ T₂) → ∋→ℕ x₁ ≡ ∋→ℕ x₂ → T₁ ≡ T₂
inv-∋→ℕ zero zero eq = refl
inv-∋→ℕ (suc x₁) (suc x₂) eq = inv-∋→ℕ x₁ x₂ (inv-suc eq)
