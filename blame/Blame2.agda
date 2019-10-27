module Blame2 where


--Syntax

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
-- -- infix  9 #_

data Type : Set where
  ι : Type
  _⇒_ : Type → Type → Type
  ⋆ : Type


data GType : Type → Set where
  G-ι :
      -------
      GType ι

  G-⇒ :
      -------------
      GType (⋆ ⇒ ⋆)

-- Contexts
-- Most of the following is as per DeBruijn

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

-- Compatibility
-- TODO: Prove grounding lemma?

infix 9 _∼_

data _∼_ : Type → Type → Set where
  C-ι :
      -----
      ι ∼ ι

  C-⋆-L : ∀ {A}
      -----
    → A ∼ ⋆

  C-⋆-R : ∀ {B}
      -----
    → ⋆ ∼ B

  C-Step : ∀ {A B A' B'}
    → A ∼ A'
    → B ∼ B'
      -------------------
    → (A ⇒ B) ∼ (A' ⇒ B')

-- Blame Labels
data Blame : Set where
  p : Blame
  q : Blame

⁻_ : Blame → Blame
⁻ p = q
⁻ q = p


data _⊢_ : Context → Type → Set where

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

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ ι

  `suc_ : ∀ {Γ}
    → Γ ⊢ ι
      ------
    → Γ ⊢ ι

  case : ∀ {Γ A}
    → Γ ⊢ ι
    → Γ ⊢ A
    → Γ , ι ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A

  blame_ : ∀ {Γ A} (P : Blame)
      -------------
    → Γ ⊢ A

  cast : ∀ {Γ A B} -- (P : Blame) (A ∼ B)
    → Γ ⊢ A -- M : A
    → (P : Blame)
    → (A ∼ B)
      -------------
    → Γ ⊢ B

_ : ∀ {Γ A} → Γ ⊢ A
_ = blame p

_ : ∅ , ι ⊢ ι
_ = cast (` Z) p (C-ι)


 -- _∶_—_⇒_ : Term → Type → Blame → Type → Term
 -- _∶_—_⇒_ :

-- -- Contexts
-- -- TODO : Decide if I wanna do de bruijn or named?
--

-- Terms
-- TODO : Find better syntax for casts
-- data Term : Set where
--   _·_     : Term → Term → Term
--   _∶_—_⇒_ : Term → Type → Blame → Type → Term
--   blame_  : Blame → Term



-- data Context : Set where
--   ∅ : Context
--   _,_ : Context → Type → Context

-- data _⊢_⦂_ : Context → Term → Type → Set where
--   ⊢cast : ∀ {Γ M A B}
--     → Γ ⊢ M ⦂ A
--     → A ∼ B
--       ------------------------
--     → Γ ⊢ (M ∶ A — p ⇒ B) ⦂ B

--   ⊢blame : ∀ {Γ A}
--       ---------------
--     → Γ ⊢ blame p ⦂ A
