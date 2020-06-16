module Type where
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Product using (∃-syntax; _,_; proj₁; _×_)
open import Data.Vec using (Vec; replicate; []; _∷_; map; zip)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)

data AscribedVec (X : Set) (P : X → Set) : {n : ℕ} → Vec X n → Set where
  []  : AscribedVec X P []
  _∷_ : ∀ {x n}
    → {xs : Vec X n}
    → (y : P x)
    → (ys : AscribedVec X P xs)
    → AscribedVec X P (x ∷ xs)
                           
infix  99 `_
infix 100 _⇒_
infix 100 _⊗_
infix 100 _⊕_

data BaseTypeCode : Set where
  unit : BaseTypeCode
  nat  : BaseTypeCode

BaseValue : BaseTypeCode → Set
BaseValue unit = ⊤
BaseValue nat = ℕ

_≟btc_ : (b1 b2 : BaseTypeCode) → Dec (b1 ≡ b2)
unit ≟btc unit = yes refl
unit ≟btc nat = no (λ ())
nat ≟btc unit = no (λ ())
nat ≟btc nat = yes refl

data TypeOp : Set where
  `_ : (b : BaseTypeCode) → TypeOp
  `⊗ : TypeOp
  `⊕ : TypeOp
  `⇒ : TypeOp

_≟to_ : (o1 o2 : TypeOp) → Dec (o1 ≡ o2)
`⊗ ≟to `⊗ = yes refl
`⊗ ≟to `⇒ = no (λ ())
`⇒ ≟to `⊗ = no (λ ())
`⇒ ≟to `⇒ = yes refl
`⊗ ≟to `⊕ = no (λ ())
`⊕ ≟to `⊗ = no (λ ())
`⊕ ≟to `⊕ = yes refl
`⊕ ≟to `⇒ = no (λ ())
`⇒ ≟to `⊕ = no (λ ())
` b₁ ≟to ` b₂ with b₁ ≟btc b₂
(` b₁ ≟to ` b₂) | yes refl = yes refl
(` b₁ ≟to ` b₂) | no ¬p = no λ { refl → ¬p refl }
` b ≟to `⊗ = no (λ ())
` b ≟to `⊕ = no (λ ())
` b ≟to `⇒ = no (λ ())
`⊗ ≟to ` b = no (λ ())
`⊕ ≟to ` b = no (λ ())
`⇒ ≟to ` b = no (λ ())

arity : TypeOp → ℕ
arity (` b) = 0
arity `⊗ = 2
arity `⊕ = 2
arity `⇒ = 2

data PreType : Set
data Type : Set

data PreType where
  _,_ : ∀ o
    → (Ts : Vec Type (arity o))
    → PreType

data Type where
  *  : Type
  `_ : (P : PreType) → Type


pattern ′_  b   = (` b) , []
pattern _⇒_ S T = `⇒ , (S ∷ T ∷ [])
pattern _⊗_ S T = `⊗ , (S ∷ T ∷ [])
pattern _⊕_ S T = `⊕ , (S ∷ T ∷ [])

data Polarity : Set where
  - : Polarity
  + : Polarity

polarity : (op : TypeOp) → Vec Polarity (arity op)
polarity (` b) = []
polarity `⊗ = + ∷ + ∷ []
polarity `⊕ = + ∷ + ∷ []
polarity `⇒ = - ∷ + ∷ []

choose : {A : Set} → Polarity → A → A → A
choose - a b = a
choose + a b = b
               
data Same : PreType → Set where
  same : ∀ P → Same P

Ground : PreType → Set
Ground P = ∃[ o ](P ≡ (o , replicate *))

-- consistency

data _~_ : (T1 T2 : Type) → Set

_~*_ : ∀ {n} → (Ts₁ Ts₂ : Vec Type n) → Set
Ts₁ ~* Ts₂ = AscribedVec (Type × Type) (λ { (S , T) → S ~ T }) (zip Ts₁ Ts₂)

data _~_ where
  ** : * ~ *
  *P : ∀ P → * ~ (` P)
  P* : ∀ P → (` P) ~ *
  PP : ∀ o {Ts₁ Ts₂}
    → (p : Ts₁ ~* Ts₂)
    → (` (o , Ts₁)) ~ (` (o , Ts₂))

*~T : ∀ {T} → * ~ T
*~T {*}   = **
*~T {` P} = *P P

T~* : ∀ {T} → T ~ *
T~* {*}   = **
T~* {` P} = P* P

~refl : ∀ T → T ~ T
~refl * = **
~refl (` (′ b)) = PP (` b) []
~refl (` S ⊗ T) = PP `⊗ (~refl S ∷ (~refl T ∷ []))
~refl (` S ⊕ T) = PP `⊕ (~refl S ∷ (~refl T ∷ []))
~refl (` S ⇒ T) = PP `⇒ (~refl S ∷ (~refl T ∷ []))

_~?_ : (T₁ T₂ : Type) → Dec (T₁ ~ T₂)
_~*?_ : ∀ {n} → (Ts₁ Ts₂ : Vec Type n) → Dec (Ts₁ ~* Ts₂)


* ~? * = yes **
* ~? (` P) = yes (*P P)
(` P) ~? * = yes (P* P)
(` (o₁ , Ts₁)) ~? (` (o₂ , Ts₂))
  with o₁ ≟to o₂
((` (o₁ , Ts₁)) ~? (` (o₂ , Ts₂))) | no ¬p = no λ { (PP o ps) → ¬p refl }
((` (o₁ , Ts₁)) ~? (` (.o₁ , Ts₂))) | yes refl
  with Ts₁ ~*? Ts₂
((` (o₁ , Ts₁)) ~? (` (.o₁ , Ts₂))) | yes refl | no ¬p
  = no λ { (PP o p) → ¬p p }
((` (o₁ , Ts₁)) ~? (` (.o₁ , Ts₂))) | yes refl | yes p
  = yes (PP o₁ p)

[] ~*? [] = yes []
(S ∷ Ss) ~*? (T ∷ Ts)
  with S ~? T
((S ∷ Ss) ~*? (T ∷ Ts)) | no ¬p = no λ { (y ∷ x) → ¬p y }
((S ∷ Ss) ~*? (T ∷ Ts)) | yes p
  with Ss ~*? Ts
((S ∷ Ss) ~*? (T ∷ Ts)) | yes p | no ¬ps = no λ { (p' ∷ ps') → ¬ps ps' }
((S ∷ Ss) ~*? (T ∷ Ts)) | yes p | yes ps = yes (p ∷ ps)

-- shallow consistency

data _⌣_ : (T1 T2 : Type) → Set where
  ** : * ⌣ *
  *P : ∀ P → * ⌣ (` P)
  P* : ∀ P → (` P) ⌣ *
  PP : ∀ o {Ss Ts} → (` (o , Ss)) ⌣ (` (o , Ts))

_⌣?_ : ∀ T₁ T₂ → Dec (T₁ ⌣ T₂)
* ⌣? * = yes **
* ⌣? (` P) = yes (*P P)
(` P) ⌣? * = yes (P* P)
(` (o₁ , Ts₁)) ⌣? (` (o₂ , Ts₂)) with o₁ ≟to o₂
((` (o₁ , Ts₁)) ⌣? (` (o₁ , Ts₂))) | yes refl = yes (PP o₁)
((` (o₁ , Ts₁)) ⌣? (` (o₂ , Ts₂))) | no ¬p = no λ { (PP o) → ¬p refl }

-- more imprecise

data _⊒_ : Type → Type → Set where
  ** : * ⊒ *
  *P : ∀ P → * ⊒ (` P)
  PP : ∀ o {Ss Ts}
    → (ps : AscribedVec (Type × Type) (λ { (S , T) → S ⊒ T }) (zip Ss Ts))
    → (` (o , Ss)) ⊒ (` (o , Ts))

-- matching

data _▹_ : Type → PreType → Set where
  same : ∀ P → (` P) ▹ P
  proj : ∀ o → * ▹ (o , replicate *)

match? : ∀ T o → Dec (∃[ Ts ](T ▹ (o , Ts)))
match? *             o = yes (replicate * , proj o)
match? (` (o' , Ts)) o with o' ≟to o
match? (` (o' , Ts)) o | yes refl = yes (Ts , same (o' , Ts))
match? (` (o' , Ts)) o | no ¬o'≡o = no λ { (_ , same .(o , _)) → ¬o'≡o refl }

▹-src : ∀ {T P} → T ▹ P → Type
▹-src {T}{P} T▹P = T

▹-dst : ∀ {T P} → T ▹ P → PreType
▹-dst {T}{P} T▹P = P

▹-dom : ∀ {A S T} → A ▹ (S ⇒ T) → Type
▹-dom {A}{S}{T} _ = S

inv-▹ : ∀ {T o} → (x y : ∃[ Ts ](T ▹ (o , Ts))) → x ≡ y
inv-▹ (fst , same .(_ , fst)) (.fst , same .(_ , fst)) = refl
inv-▹ (.(replicate *) , proj o) (.(replicate *) , proj .o) = refl

match→consistency : ∀ {T P} → T ▹ P → T ~ (` P)
match→consistency (same P) = ~refl (` P)
match→consistency (proj o) = *P (o , replicate *)

join : Type → Type → Type
join * T = *
join (` P) * = *
join (` (o₁ , Ts₁)) (` (o₂ , Ts₂)) with o₁ ≟to o₂
join (` (o₁ , Ts₁)) (` (o₂ , Ts₂)) | no ¬p    = *
join (` (o₁ , Ts₁)) (` (o₂ , Ts₂)) | yes refl = ` (o₁ , join* Ts₁ Ts₂)
  where
  join* : ∀ {n} → Vec Type n → Vec Type n → Vec Type n
  join* [] [] = []
  join* (T₁ ∷ Ts₁) (T₂ ∷ Ts₂) = join T₁ T₂ ∷ join* Ts₁ Ts₂
