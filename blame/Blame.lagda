```
module Blame where

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
  P : Blame
  Q : Blame

⁻_ : Blame → Blame
⁻_ P = Q
⁻_ Q = P
```
