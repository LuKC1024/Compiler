module Lang.Cast.Dynamics where

open import Type
open import Variable
open import BlameLabel
open import Lang.Cast.Statics

open import Data.Product
open import Data.Sum
open import Data.Vec hiding (_>>=_; lookup)
open import Data.Unit
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- FFI

FFI : Set
FFI = ∃[ n ](Vec BaseTypeCode n × BaseTypeCode)

FFI-agda : ∀ {n} → Vec BaseTypeCode n → BaseTypeCode → Set
FFI-agda [] T = BaseValue T
FFI-agda (S ∷ Ss) T = BaseValue S → FFI-agda Ss T

FFI-gtlc : ∀ {n} → Vec BaseTypeCode n → BaseTypeCode → Type
FFI-gtlc [] T = ` (′ T)
FFI-gtlc (S ∷ Ss) T = ` ((` (′ S)) ⇒ FFI-gtlc Ss T)

data Value : Type → Set
PreValue : PreType → Set

data Env : Context → Set where
  []  : Env ∅
  _∷_ : ∀ {Γ T}
    → (v : Value T)
    → Env Γ
    → Env (Γ , T)

lookup : ∀ {Γ T} → (x : Γ ∋ T)(ρ : Env Γ) → Value T
lookup zero (v ∷ ρ) = v
lookup (suc x) (v ∷ ρ) = lookup x ρ

data Value where

  dyn : (l : BlameLabel)
    → (o : TypeOp)
    → (v : PreValue (o , replicate *))
    → Value *
    
  `_  : ∀ {P}
    → (v : PreValue P)
    → Value (` P)

data PairValue : Type → Type → Set where
  _,_ : ∀ {S T} → Value S → Value T → PairValue S T
  _⟪_⊗_⟫ : ∀ {S₁ T₁ S₂ T₂}
    → (v : PairValue S₁ T₁)
    → (c : Cast S₁ S₂)
    → (d : Cast T₁ T₂)
    → PairValue S₂ T₂

data EitherValue : Type → Type → Set where
  inj₁ : ∀ {S T} → (v : Value S) → EitherValue S T
  inj₂ : ∀ {S T} → (v : Value T) → EitherValue S T
  _⟪_⊕_⟫ : ∀ {S₁ T₁ S₂ T₂}
    → (v : EitherValue S₁ T₁)
    → (c : Cast S₁ S₂)
    → (d : Cast T₁ T₂)
    → EitherValue S₂ T₂

data ClosValue : Type → Type → Set where

  prim : ∀ n {S Ss T}
    → (v : FFI-agda {suc n} (S ∷ Ss) T)
    → ClosValue (` (′ S)) (FFI-gtlc Ss T)
    
  _,_ : ∀ {Γ S T}
    → (e : (Γ , S) ⊢ T)
    → (ρ : Env Γ)
    → ClosValue S T
    
  _⟪_⇒_⟫ : ∀ {S₁ T₁ S₂ T₂}
    → (v : ClosValue S₁ T₁)
    → (c : Cast S₂ S₁)
    → (d : Cast T₁ T₂)
    → ClosValue S₂ T₂

PreValue (′ b) = BaseValue b
PreValue (S ⊗ T) = PairValue S T
PreValue (S ⊕ T) = EitherValue S T
PreValue (S ⇒ T) = ClosValue S T

FFI-quote : ∀ n → {Ss : Vec BaseTypeCode n}{T : BaseTypeCode}
  → FFI-agda Ss T
  → Value (FFI-gtlc Ss T)
FFI-quote zero    {[]}     v = ` v
FFI-quote (suc n) {S ∷ Ss} v = ` prim n v

data ErrorType : Set where
  blame : BlameLabel → BlameLabel → ErrorType
  timeout : ErrorType

data Error (A : Set) : Set where
  just : A → Error A
  error : ErrorType → Error A

_>>=_ : ∀ {A B} → Error A → (A → Error B) → Error B
just x  >>= f = f x
error x >>= f = error x

inject : (P : PreType)(l : BlameLabel)(v : Value (` P)) → Value *
inject (′ b)   l (` v) = dyn l (` b) v
inject (S ⊗ T) l (` v) = dyn l `⊗ (v ⟪ S ⟹[ l ] * ⊗ T ⟹[ l ] * ⟫)
inject (S ⊕ T) l (` v) = dyn l `⊕ (v ⟪ S ⟹[ l ] * ⊕ T ⟹[ l ] * ⟫)
inject (S ⇒ T) l (` v) = dyn l `⇒ (v ⟪ * ⟹[ l ] S ⇒ T ⟹[ l ] * ⟫)

project : (v : Value *)(l : BlameLabel)(P : PreType) → Error (Value (` P))
project (dyn lᵢ o₁ v) lₚ (o₂ , Ts) with o₁ ≟to o₂
project (dyn lᵢ o₁ v) lₚ (o₂ , Ts) | no ¬p = error (blame lᵢ lₚ)
project (dyn lᵢ (` b) v) lₚ (′ b)  | yes refl = just (` v)
project (dyn lᵢ `⊗ v) lₚ (S ⊗ T) | yes refl = just (` (v ⟪ * ⟹[ lₚ ] S ⊗ * ⟹[ lₚ ] T ⟫))
project (dyn lᵢ `⊕ v) lₚ (S ⊕ T) | yes refl = just (` (v ⟪ * ⟹[ lₚ ] S ⊕ * ⟹[ lₚ ] T ⟫))
project (dyn lᵢ `⇒ v) lₚ (S ⇒ T) | yes refl = just (` (v ⟪ S ⟹[ lₚ ] * ⇒ * ⟹[ lₚ ] T ⟫))

proxy : (l : BlameLabel)(o : TypeOp)(Ss Ts : Vec Type (arity o))(v : Value (` (o , Ss))) → Value (` (o , Ts))
proxy l (` b) [] [] v = v
proxy l `⊗ (S₁ ∷ T₁ ∷ []) (S₂ ∷ T₂ ∷ []) (` v) = ` (v ⟪ S₁ ⟹[ l ] S₂ ⊗ T₁ ⟹[ l ] T₂ ⟫)
proxy l `⊕ (S₁ ∷ T₁ ∷ []) (S₂ ∷ T₂ ∷ []) (` v) = ` (v ⟪ S₁ ⟹[ l ] S₂ ⊕ T₁ ⟹[ l ] T₂ ⟫)
proxy l `⇒ (S₁ ∷ T₁ ∷ []) (S₂ ∷ T₂ ∷ []) (` v) = ` (v ⟪ S₂ ⟹[ l ] S₁ ⇒ T₁ ⟹[ l ] T₂ ⟫)

RtCast : Type → Type → Set
RtCast S T = Value S → Error (Value T)

⟦_⟧ : ∀ {S T}
  → (c : Cast S T)
  → RtCast S T
⟦ S ⟹[ l ] T ⟧ v with S ⌣? T
⟦ S ⟹[ l ] T ⟧ v | no ¬p = error (blame l l)
⟦ * ⟹[ l ] * ⟧ v | yes ** = just v
⟦ * ⟹[ l ] (` P) ⟧ v | yes (*P P) = project v l P
⟦ (` P) ⟹[ l ] * ⟧ v | yes (P* P) = just (inject P l v)
⟦ (` (o , Ss)) ⟹[ l ] (` (o , Ts)) ⟧ v | yes (PP o) = just (proxy l o Ss Ts v)

_⨟_ : ∀ {T1 T2 T3} → RtCast T1 T2 → RtCast T2 T3 → RtCast T1 T3
(s ⨟ t) v = do
  v ← s v
  t v

eval : ∀ {Γ T Z}
  → (gas : ℕ)(e : Γ ⊢ T)(ρ : Env Γ)(s : RtCast T Z)
  → Error (Value Z)
  
do-app : ∀ {S T Z}
  → (gas : ℕ)
  → (f : ClosValue S T)
  → (a : Value S)
  → (s : RtCast T Z)
  → Error (Value Z)
do-app gas (prim n v) (` a) s = s (FFI-quote n (v a))
do-app gas (e , ρ)       a s = eval gas e (a ∷ ρ) s
do-app gas (f ⟪ c ⇒ d ⟫) a s = do
  v ← ⟦ c ⟧ a
  do-app gas f v (⟦ d ⟧ ⨟ s)

do-which : ∀ {Γ S₁ S₂ T₁ T₂ T Z}
  → (gas : ℕ)(b : EitherValue S₁ S₂)
  → (s₁ : RtCast S₁ T₁)(e₁ : Γ , T₁ ⊢ T)
  → (s₂ : RtCast S₂ T₂)(e₂ : Γ , T₂ ⊢ T)
  → (ρ : Env Γ)(s : RtCast T Z)
  → Error (Value Z)
do-which gas (inj₁ v) s₁ e₁ s₂ e₂ ρ s = do
  v ← s₁ v
  eval gas e₁ (v ∷ ρ) s
do-which gas (inj₂ v) s₁ e₁ s₂ e₂ ρ s = do
  v ← s₂ v
  eval gas e₂ (v ∷ ρ) s
do-which gas (v ⟪ c₁ ⊕ c₂ ⟫) s₁ e₁ s₂ e₂ ρ s =
  do-which gas v (⟦ c₁ ⟧ ⨟ s₁) e₁ (⟦ c₂ ⟧ ⨟ s₂) e₂ ρ s

do-car : ∀ {S T}
  → (p : PairValue S T)
  → Error (Value S)
do-car (u , v) = just u
do-car (p ⟪ c ⊗ d ⟫) = do
  v ← do-car p
  ⟦ c ⟧ v
  
do-cdr : ∀ {S T}
  → (p : PairValue S T)
  → Error (Value T)
do-cdr (u , v) = just v
do-cdr (p ⟪ c ⊗ d ⟫) = do
  v ← do-cdr p
  ⟦ d ⟧ v

eval zero e ρ s = error timeout
eval (suc gas) (var x) ρ s = s (lookup x ρ)
eval (suc gas) (fun S T e) ρ s = s (` (e , ρ))
eval (suc gas) (app e₁ e₂) ρ s = do
  (` v₁) ← eval gas e₁ ρ just
  v₂ ← eval gas e₂ ρ just 
  do-app gas v₁ v₂ s
eval (suc gas) (cons e₁ e₂) ρ s = do
  v₁ ← eval gas e₁ ρ just
  v₂ ← eval gas e₂ ρ just
  s (` (v₁ , v₂))
eval (suc gas) (car e) ρ s = do
  (` v) ← eval gas e ρ just
  v ← do-car v
  s v
eval (suc gas) (cdr e) ρ s = do
  (` v) ← eval gas e ρ just
  v ← do-cdr v
  s v
eval (suc gas) (e ⟨ c ⟩) ρ s = eval gas e ρ (⟦ c ⟧ ⨟ s)
eval (suc gas) (inj₁ e) ρ s = do
  v ← eval gas e ρ just
  s (` (inj₁ v))
eval (suc gas) (inj₂ e) ρ s = do
  v ← eval gas e ρ just
  s (` (inj₂ v))
eval (suc gas) (which e e₁ e₂) ρ s = do
  ` v ← eval gas e ρ just
  do-which gas v just e₁ just e₂ ρ s
