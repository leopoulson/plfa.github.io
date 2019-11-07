```
module Blame where

import Relation.Binary.PropositionalEquality as Eq

open import Data.String using (String; _≟_) -- for Blame labels
open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open Eq using (_≡_; _≢_)
```

Types and Ground Types

```
infixr 7 _⇒_

data Type : Set where
  ι : Type
  _⇒_ : Type → Type → Type
  ★ : Type

data GType : Type → Set where
  G-ι :
    -------
    GType ι

  G-⇒ :
    -------------
    GType (★ ⇒ ★)
```

### Compatibility

```
infixl 6 _∼_

data _∼_ : Type → Type → Set where
  C-ι :
      -----
      ι ∼ ι

  C-★-A : ∀ {A}
      -----
    → A ∼ ★

  C-★-B : ∀ {B} {G : GType B}
      -----
    → ★ ∼ B

  C-Step : ∀ {A B A' B'}
    → A ∼ A'
    → B ∼ B'
      -------------------
    → (A ⇒ B) ∼ (A' ⇒ B')

-- grounding-1 : ∀ {A T : Type} {G : GType T} → A ≢ ★
--   → ∃[ G ] (A ∼ G × ∀ {F} A ∼ F → F ≡ G)
-- grounding-1 x = {!!} , {!!}


-- data unique-grounding : Type → Type → Set where

--   ug : ∀ {A G}
--     → A ≢ ★
--     → A ≢ G
--     → A ∼ G
--       ------
--     → unique-grounding A G

record unique-grounding (A G : Type) : Set where
  field
    A≢★ : A ≢ ★
    A≢G : A ≢ G
    A∼G : A ∼ G
open unique-grounding


```

Blame Labels

```
Blame : Set
Blame = String

-- infix 3 -_

-- data Neg : Blame → Set where
--   -_ : ∀ {B : Blame}

--     → - B
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
infix  5 ƛ_
infixl 7 _·_
infix  9 `_
data _⊢_ : Context → Type → Set where

  k : ∀ {Γ}
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

  ƛ_  : ∀ {Γ A B}
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

  V-k : ∀ {Γ}
      ---------------
    → Value {Γ = Γ} k

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-⇒ : ∀ {Γ A B A′ B′} {P : Blame} {V : Γ ⊢ A ⇒ B} {comp : A ⇒ B ∼ A′ ⇒ B′}
    → Value V
    -- → (A ⇒ B ∼ A′ ⇒ B′)
      -----------------------
    → Value (cast V P (comp))

  V-★ : ∀ {Γ T} {G : GType T} {P : Blame} {V : Γ ⊢ T} {A : Type}
    → Value V

    → Value (cast V P (C-★-A))
```


### Reduction

```

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ιι : ∀ {Γ} {P : Blame} {V : Γ ⊢ ι}
      -------------------
    → cast V P (C-ι) —→ V

  ★★ : ∀ {Γ} {P : Blame} {V : Γ ⊢ ★}
      -------------------
    → cast V P (C-★-A) —→ V

  A* : ∀ {Γ A B} {P : Blame} {V : Γ ⊢ A}
    → (ug : unique-grounding A B)
    → cast V P (C-★-A) —→ cast (cast V P (A∼G ug)) P C-★-A
```
