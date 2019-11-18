```
module Blame where

import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; ∃!) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open Eq using (_≡_; _≢_; refl; cong₂)

open import Iff using (_⇔_)
open import Types using (Type; GType; ι; ★; _⇒_; G-ι; G-⇒; Blame; `_; not; safe; <+; <-; <≢; cast; Cast)
```

### Type Compatibility

```
infixl 6 _∼_

data _∼_ : Type → Type → Set where
  C-ι :
      -----
      ι ∼ ι

  C-A-★ : ∀ (A)
      -----
    → A ∼ ★

  C-★-B : ∀ (B)
      -----
    → ★ ∼ B

  C-Step : ∀ {A B A' B'}
    → A ∼ A'
    → B ∼ B'
      -------------------
    → (A ⇒ B) ∼ (A' ⇒ B')

∼-sym : ∀ {A B} → A ∼ B → B ∼ A
∼-sym C-ι = C-ι
∼-sym (C-A-★ A) = C-★-B A
∼-sym (C-★-B B) = C-A-★ B
∼-sym (C-Step x x₁) = C-Step (∼-sym x) (∼-sym x₁)

record unique-grounding (A G : Type) : Set where
  field
    GT : GType G
    A≢★ : A ≢ ★
    A≢G : A ≢ G
    A∼G : A ∼ G
open unique-grounding

ground-unique : ∀ A → A ≢ ★ → ∃! _≡_ (λ G → A ∼ G × GType G)
ground-unique ι ne = ⟨ ι , ⟨ ⟨ C-ι , G-ι ⟩ , (λ { ⟨ C-ι , G-ι ⟩ → refl } ) ⟩ ⟩
ground-unique ★ ne = ⊥-elim (ne refl)
ground-unique (t ⇒ t₁) ne = ⟨ ★ ⇒ ★ , ⟨ ⟨ C-Step (C-A-★ t) (C-A-★ t₁) , G-⇒ ⟩ , (λ { ⟨ _ , G-⇒ ⟩ → refl }) ⟩ ⟩

ground-to : ∀ {G H} (GE : GType G) (HE : GType H) → (G ∼ H) → (G ≡ H)
ground-to G-ι G-ι G∼H = refl
ground-to G-⇒ G-⇒ G∼H = refl

ground-from : ∀ {G H} (GE : GType G) (HE : GType H) → (G ≡ H) → (G ∼ H)
ground-from G-ι G-ι refl = C-ι
ground-from G-⇒ G-⇒ refl = C-Step (C-A-★ ★) (C-A-★ ★)

ground-eq : ∀ {G H} (GE : GType G) (HE : GType H) → (G ∼ H) ⇔ (G ≡ H)
ground-eq x y = record { to = ground-to x y ; from = ground-from x y }
```


Terms

We first need to define contexts and so on.

```
infix 4 _∋_
infixl 5 _,_

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```

Now we can do terms too

```
infix  4 _⊢_
infix  5 ƛ_∙_
infixl 7 _·_
infix  8 blame_
infix  9 `_
data _⊢_ : Context → Type → Set where

  k : ∀ {Γ}
    → Γ ∋ ι
      -----
    → Γ ⊢ ι

  -- TODO
  -- op : ∀ {Γ}
  --   → Vect n ι
  --     -----
  --   → Γ ⊢ ι

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_∙_  : ∀ {Γ  B} (A)
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  blame_ : ∀ {Γ A}
    → (P : Blame)
      -------------
    → Γ ⊢ A

  cast : ∀ {Γ A B}
    → Γ ⊢ A
    → (P : Blame)
    → (A ∼ B)
      -------------
    → Γ ⊢ B
```

### Values

```
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-k : ∀ {Γ x}
      ---------------
    → Value {Γ = Γ} {A = ι} (k x)

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ A ∙ N)

  V-⇒ : ∀ {Γ A B A′ B′} {P : Blame} {V : Γ ⊢ A ⇒ B} {comp : A ⇒ B ∼ A′ ⇒ B′}
    → Value V
    -- → (A ⇒ B ∼ A′ ⇒ B′)
      -----------------------
    → Value (cast V P (comp))

  V-★ : ∀ {Γ G} {GT : GType G} {P : Blame} {V : Γ ⊢ G}
    → Value V
      --------------------------
    → Value (cast V P (C-A-★ G))
```



### Substitution

```
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (k x)          = k (ρ x)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ T ∙ N)      =  ƛ T ∙ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (blame P)      = blame P
rename ρ (cast T P C)   = cast (rename ρ T) P C

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (k x)          = σ x
subst σ (` x)          = σ x
subst σ (ƛ T ∙ N)      =  ƛ T ∙ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (blame P)      = blame P
subst σ (cast T P x)   = cast (subst σ T) P x

_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x

```


### Eval Contexts

```
data EC : Context → Type → Type → Set where
  ■M : ∀ {Γ A B}
    → Γ ⊢ A
      --------------
    → EC Γ (A ⇒ B) B

  V■ : ∀ {Γ A B} (V : Γ ⊢ A ⇒ B) {_ : Value V}
    -- → Value V
    -- → Γ ⊢ A ⇒ B
      ---------
    → EC Γ A B

  cast■ : ∀ {Γ A B}
      (A∼B : A ∼ B)
    → (P : Blame)
      -------------
    → EC Γ A B

_E[_] : ∀ {Γ A B} → EC Γ A B → Γ ⊢ A → Γ ⊢ B
■M M E[ T ] = T · M
V■ V E[ T ] = V · T
cast■ A∼B P E[ T ] = cast T P A∼B
```

### Reduction

```

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      ------------------------
    → (ƛ A ∙ N) · V —→ N [ V ]
   
  ιι : ∀ {Γ} {P : Blame} {V : Γ ⊢ ι}
    → Value V
      -------------------
    → cast V P (C-ι) —→ V

  wrap : ∀ {Γ A B A′ B′ W} {A∼A′ : A ∼ A′} {B∼B′ : B ∼ B′} {V : Γ ⊢ A ⇒ B} {P : Blame}
    → Value V
      ----------------------------------------------------
    → (cast V P (C-Step A∼A′ B∼B′)) · W —→
           cast (V · (cast W (not P) (∼-sym A∼A′))) P (B∼B′)

  ★★ : ∀ {Γ} {P : Blame} {V : Γ ⊢ ★}
    → Value V
      -------------------
    → cast V P (C-A-★ ★) —→ V

  A* : ∀ {Γ A G} {GT : GType G} {P : Blame} {V : Γ ⊢ A}
    → Value V
    → (ug : unique-grounding A G)
      ----------------------------------------------------------
    → cast V P (C-A-★ A) —→ cast (cast V P (A∼G ug)) P (C-A-★ G)

  *A : ∀ {Γ A G} {_ : GType G} {P : Blame} {V : Γ ⊢ ★}
    → Value V
    → (ug : unique-grounding A G)
      ------------------------------------------------------------------
    → cast V P (C-★-B A) —→ cast (cast V P (C-★-B G)) P (∼-sym (A∼G ug))

  G★G : ∀ {Γ G} {_ : GType G} {P Q : Blame} {V : Γ ⊢ G}
    → Value V
      -----------------------------------------------
    → cast (cast V P (C-A-★ G)) Q (C-★-B G) —→ V

  G★H : ∀ {Γ G H} {_ : GType G} {_ : GType H} {P Q : Blame} {V : Γ ⊢ G}
    → Value V
    → G ≢ H
      -----------------------------------------------
    → cast (cast V P (C-A-★ G)) Q (C-★-B H) —→ blame Q

  -- E→E : ∀ {Γ A B} (E : EC Γ A B) {M M′ : Γ ⊢ A}
  --   → M —→ M′
  --     -------------------
  --   → E E[ M ] —→ E E[ M′ ]

  -- E→B : ∀ {Γ A B} (E : EC Γ A B) {P : Blame}
  --     ------------------------
  --   → E E[ blame P ] —→ blame P

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      --------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  ξ-cast : ∀ {Γ A B P} (A∼B : A ∼ B) {M M′ : Γ ⊢ A}
    → M —→ M′
    -------------------------------
    → cast M P A∼B —→ cast M′ P A∼B

  -- B-·₁ : ∀ {Γ A P B} {M : Γ ⊢ A} (blame P : Γ ⊢ A ⇒ B)
  --   --------------------------
  --   → ((blame P) · M) —→ blame P

  B-·₂ : ∀ {Γ A B P} {V : Γ ⊢ A ⇒ B}
    → Value V
    --------------------------
    → V · (blame P) —→ blame P

  B-cast : ∀ {A B P Q} {A∼B : A ∼ B}
    → cast (blame P) Q A∼B —→ blame P


-- Reflexive and transitive closure

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

FAILURE

```
-- failure : ∀ {Γ A B G H} {V : Γ ⊢ A} {_ : Value V} (A≢★ : A ≢ ★) (A∼G : A ∼ G) (G≠H : G ≢ H) {P Q R S : Blame}
--   → cast (cast (cast (cast V P A∼G) Q (C-A-★ G)) R (C-★-B H)) S (∼-sym {!!}) —↠ blame P
-- failure = {!!}

-- failure-lem : ∀ {Γ M A B P} → (cast M P (A ∼ B)) → (A ∼ B) → M
-- failure-lem c A∼B = ?
```

### Embedding Dynamically-typed LC

```
infix 5 ƛ_
infix  4 _D⊢_
data _D⊢_ : Context → Type → Set where

  k : ∀ {Γ}
    → Γ ∋ ι
      -----
    → Γ D⊢ ι

  -- TODO
  -- op : ∀ {Γ}
  --   → Vect n ι
  --     -----
  --   → Γ ⊢ ι

  `_ : ∀ {Γ}
    → Γ ∋ ★
      -----
    → Γ D⊢ ★

  ƛ_  : ∀ {Γ}
    → Γ , ★ D⊢ ★
      ---------
    → Γ D⊢ ★

  _·_ : ∀ {Γ}
    → Γ D⊢ ★ ⇒ ★
    → Γ D⊢ ★
      ---------
    → Γ D⊢ ★

⌈_⌉ : ∀ {Γ A} → Γ D⊢ A → Blame → Γ ⊢ ★
⌈ k x ⌉ P = cast (k x) P (C-A-★ ι)
⌈ ` x ⌉ _ = ` x
⌈ ƛ t ⌉ P = cast (ƛ ★ ∙  ⌈ t ⌉ P) P (C-A-★ (★ ⇒ ★))
⌈ L · M ⌉ P = (cast (⌈ L ⌉ P) P (C-★-B (★ ⇒ ★))) · ⌈ M ⌉ P
```

Determinism!


cong₃ : ∀ {A B C D} (f : A → B → C → D) {x y : A} {u v : B} {t s : C} → x ≡ y → u ≡ v → t ≡ s → f x u t ≡ f y v s
cong₃ f refl refl refl = refl

V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-⇒ v) (ξ-cast _ x) = V¬—→ v x
-- we can get false here from the fact that A≢G, A here is some ground type,
-- and A∼G, so G≡H, which is a contradiction
-- V¬—→ (V-★ GT1 V) (A* record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = A≢G (ground-to GT1 GT A∼G)
V¬—→ (V-★ V) (ξ-cast _ x) = V¬—→ V x
V¬—→ (V-★ V) (A* V-k record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = A≢G (ground-to G-ι GT A∼G)
V¬—→ (V-★ x) (A* V-ƛ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = {!!}
V¬—→ (V-★ x) (A* (V-⇒ y) record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = {!!}

determinism : ∀ {Γ A} {M : Γ ⊢ A} {N L : Γ ⊢ A} → M —→ N → M —→ L → N ≡ L
determinism (β-ƛ x) (β-ƛ x₁) = refl
determinism (β-ƛ V) (ξ-·₂ _ M—→M′) = ⊥-elim (V¬—→ V M—→M′)

determinism (ιι _) (ιι _) = refl
determinism (ιι V-k) (ξ-cast c ML) = ⊥-elim (V¬—→ V-k ML)

determinism (wrap x) (wrap x₁) = refl
determinism (wrap V) (ξ-·₁ ML) = ⊥-elim (V¬—→ (V-⇒ V) ML )
determinism (wrap x) (ξ-·₂ x₁ ML) = {!!}
determinism (wrap x) (B-·₂ x₁) = determinism {!!} ((B-·₂ x₁))

determinism (★★ x) (★★ x₁) = refl
determinism (★★ x) (A* x₁ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢★ refl)
determinism (★★ V) (ξ-cast (C-A-★ ★) ML) = ⊥-elim (V¬—→ V ML)

determinism (A* x record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) (★★ V) = ⊥-elim (A≢★ refl)
determinism (A* x record { GT = GT₁ ; A≢★ = A≢★₁ ; A≢G = A≢G₁ ; A∼G = A∼G₁ })
            (A* x₁ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = {!!}
determinism (A* V ug) (ξ-cast (C-A-★ A) ML) = ⊥-elim (V¬—→ V ML)

determinism (*A x ug) (*A x₁ ug₁) = {!!}
determinism (*A V ug) (G★G x₁) = {!!}
determinism (*A x ug) (G★H x₁ x₂) = {!!}
determinism (*A V ug) (ξ-cast _ ML) = ⊥-elim (V¬—→ V ML)

determinism (G★G x) (*A x₁ ug) = {!!}
determinism (G★G x) (G★G x₁) = refl
determinism (G★G V) (G★H V′ A≢A) = ⊥-elim (A≢A refl)
determinism (G★G V) (ξ-cast (C-★-B B) ML) = ⊥-elim (V¬—→ (V-★ V) ML)

determinism (G★H V G≢A) (*A x₂ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = {!!}
determinism (G★H _ A≢A) (G★G _) = ⊥-elim (A≢A refl)
determinism (G★H x x₁) (G★H x₂ x₃) = refl
determinism (G★H V _) (ξ-cast _ ML) = ⊥-elim (V¬—→ (V-★ V) ML )

determinism (ξ-·₁ MN) (wrap V) = ⊥-elim (V¬—→ (V-⇒ V) MN)
determinism (ξ-·₁ MN) (ξ-·₁ ML) = refl
determinism (ξ-·₁ MN) (ξ-·₂ V ML) = ⊥-elim (V¬—→ V MN)
determinism (ξ-·₁ MN) (B-·₂ V) = ⊥-elim (V¬—→ V MN)

determinism (ξ-·₂ _ MN) (β-ƛ V) = ⊥-elim (V¬—→ V MN)
determinism (ξ-·₂ V2 MN) (wrap V) = {!!}
determinism (ξ-·₂ V MN) (ξ-·₁ ML) = ⊥-elim (V¬—→ V ML)
determinism (ξ-·₂ V MN) (ξ-·₂ x₁ ML) = cong₂ _·_ refl (determinism MN ML)

determinism (ξ-cast _ MN) (ιι V) = ⊥-elim (V¬—→ V MN)
determinism (ξ-cast _ MN) (★★ V) = ⊥-elim (V¬—→ V MN )
determinism (ξ-cast _ MN) (A* V ug) = ⊥-elim (V¬—→ V MN)
determinism (ξ-cast _ MN) (*A V ug) = ⊥-elim (V¬—→ V MN)
determinism (ξ-cast _ MN) (G★G V) = ⊥-elim (V¬—→ (V-★ V) MN)
determinism (ξ-cast _ MN) (G★H V x₁) = ⊥-elim (V¬—→ (V-★ V) MN)
determinism (ξ-cast C MN) (ξ-cast .C ML) = cong₃ cast (determinism MN ML) refl refl

determinism (B-·₂ x) (wrap x₁) = {!!}
determinism (B-·₂ V) (ξ-·₁ ML) = ⊥-elim (V¬—→ V ML )
determinism (B-·₂ x) (B-·₂ x₁) = refl

determinism (B-cast) (B-cast) = refl




Blame safety

```
data safe-term : ∀ {Γ A} → Γ ⊢ A → Blame → Set where

  safe-k : ∀ {Γ x}
    → (P : Blame)
      ---------------------
    → safe-term {Γ} (k x) P

  safe-` : ∀ {Γ A}
    → (x : Γ ∋ A)
    → (P : Blame)
      -------------------------
    → safe-term {Γ} {A} (` x) P

  safe-ƛ : ∀ {Γ′ B C P} {N : Γ′ , C ⊢ B}
    → safe-term N P
      ---------------------
    → safe-term (ƛ C ∙ N) P

  safe-· : ∀ {Γ A B P} {M : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
    → safe-term M P
    → safe-term N P
      -------------------
    → safe-term (M · N) P

  safe-blame : ∀ {Γ A Q}
    → (P : Blame)
      -----------------------------
    → safe-term {Γ} {A} (blame P) Q

  safe-cast : ∀ {Γ A B P P′ Q} {M : Γ ⊢ A} {C : Cast A B P′}
    → safe-term M P
    → safe C Q
    → (A∼B : A ∼ B)
      ---------------------------
    → safe-term (cast M P′ A∼B) Q


blame-safety : ∀ {Γ A} {Q : Blame} {M N : Γ ⊢ A} → safe-term M Q → M —→ N → safe-term N Q
blame-safety (safe-· M N) (β-ƛ x) = {!!}
blame-safety (safe-· (safe-cast {C = C} M Cast (C-Step A∼A′ B∼B′)) N) (wrap x) =
    safe-cast (safe-· M (safe-cast N {!!} (∼-sym A∼A′))) {!!} B∼B′
-- blame-safety (safe-· (safe-cast {C = C} M (<+ P x₁) (C-Step A∼A′ B∼B′)) N) (wrap x) =
--     safe-cast (safe-· M (safe-cast N {!!} (∼-sym A∼A′))) {!!} B∼B′
-- blame-safety (safe-· (safe-cast M (<- x₁) (C-Step A∼A′ B∼B′)) N) (wrap x) =
--     safe-cast (safe-· M (safe-cast N {!!} (∼-sym A∼A′))) {!!} B∼B′
-- blame-safety (safe-· (safe-cast M (<≢ x₁ x₂) (C-Step A∼A′ B∼B′)) N) (wrap x) =
--     safe-cast (safe-· M (safe-cast N {!!} (∼-sym A∼A′))) {!!} B∼B′
blame-safety (safe-· M N) (ξ-·₁ red) = safe-· (blame-safety M red) N
blame-safety (safe-· M N) (ξ-·₂ x red) = safe-· M (blame-safety N red)
blame-safety (safe-· _ (safe-blame P)) (B-·₂ x) = safe-blame P

blame-safety (safe-cast st x C-ι) (ιι x₁) = {!!}
blame-safety (safe-cast st x (C-A-★ ★)) (★★ x₁) = {!st!}
blame-safety (safe-cast st x (C-A-★ A)) (A* x₁ ug) = {!!}
blame-safety (safe-cast st x (C-★-B B)) (*A x₁ ug) = {!!}
blame-safety (safe-cast st x (C-★-B B)) (G★G x₁) = {!!}
blame-safety (safe-cast st x (C-★-B B)) (G★H x₁ x₂) = {!!}
blame-safety (safe-cast st x A∼B) (ξ-cast .A∼B red) = {!!}
blame-safety (safe-cast st x A∼B) B-cast = {!!}

```
