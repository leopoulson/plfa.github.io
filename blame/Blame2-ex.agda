module Blame2-ex where


open import Data.String using (String)
--Syntax

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

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

infix  5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

Id : Set
Id = String

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term


-- Reduction

-- infix 2 _—→_

-- data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
--   E-ι :
