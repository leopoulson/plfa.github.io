module Blame2 where


--Syntax

infix 4 _⇒_

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

-- Terms
-- TODO : Rest of STLC Lol
-- TODO : Find better syntax for casts
data Term : Set where
  _·_     : Term → Term → Term
  _∶_—_⇒_ : Term → Type → Blame → Type → Term
  blame_  : Blame → Term

-- Contexts
-- TODO : Decide if I wanna do de bruijn or named?
data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢cast : ∀ {Γ M A B}
    → Γ ⊢ M ⦂ A
    → A ∼ B
      ------------------------
    → Γ ⊢ (M ∶ A — p ⇒ B) ⦂ B

  ⊢blame : ∀ {Γ A}
      ---------------
    → Γ ⊢ blame p ⦂ A
