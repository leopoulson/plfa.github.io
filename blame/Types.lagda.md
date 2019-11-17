```
module Types where

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

-- open import Function.Equivalence using (_⇔_)
open import Iff using (_⇔_)
```

In which we think about Types and Subtypes

# Types

```
infixr 7 _⇒_

data Type : Set where
  ι : Type
  ★ : Type
  _⇒_ : Type → Type → Type

data GType : Type → Set where
  G-ι :
    -------
    GType ι

  G-⇒ :
    -------------
    GType (★ ⇒ ★)
```

# Subtypes

```

infix 5 _<:_
infix 5 _<:⁺_
infix 5 _<:⁻_
infix 5 _<:ₙ_
data _<:_ : Type → Type → Set where
  <ι :
      ------
      ι <: ι

  <⇒ : ∀ {A B A′ B′}
    → A′ <: A
    → B  <: B′
      ----------------
    → A ⇒ B <: A′ ⇒ B′

  <★ :
      ------
      ★ <: ★

  <G : ∀ {A G}
    → A <: G
    → (GT : GType G)
      ------
    → A <: ★


data _<:⁻_ : Type → Type → Set

data _<:⁺_ : Type → Type → Set where
  <⁺ι :
      -------
      ι <:⁺ ι

  <⁺⇒ : ∀ {A B A′ B′}
    → A′ <:⁻ A
    → B  <:⁺ B′
      -----------------
    → A ⇒ B <:⁺ A′ ⇒ B′

  <⁺★ : ∀ {A}
      -------
    → A <:⁺ ★


data _<:⁻_ where
  <⁻ι :
      -------
      ι <:⁻ ι

  <⁻⇒ : ∀ {A B A′ B′}
    → A′ <:⁺ A
    → B  <:⁻ B′
      -----------------
    → A ⇒ B <:⁻ A′ ⇒ B′

  <⁻★ : ∀ {B}
      -------
    → ★ <:⁻ B

  <⁻G : ∀ {A G}
    → A <:⁻ G
    → GType G
      -------
    → A <:⁻ ★

data _<:ₙ_ : Type → Type → Set where
  <ₙι :
      -------
      ι <:ₙ ι

  <ₙ⇒ : ∀ {A B A′ B′}
    → A <:ₙ A′
    → B <:ₙ B′
      -----------------
    → A ⇒ B <:ₙ A′ ⇒ B′

  <ₙ★ : ∀ {A}
      -------
    → A <:ₙ ★
```

## Subtyping Lemma

```
tangram-to : ∀ {A B} → A <: B → (A <:⁺ B × A <:⁻ B)
tangram-to <ι = ⟨ <⁺ι , <⁻ι ⟩
tangram-to (<⇒ A′<A B<B′) = ⟨ <⁺⇒ (proj₂ (tangram-to A′<A)) (proj₁ (tangram-to B<B′)) , <⁻⇒ (proj₁ (tangram-to A′<A)) (proj₂ (tangram-to B<B′)) ⟩
tangram-to <★ = ⟨ <⁺★ , <⁻★ ⟩
tangram-to (<G x GT) = ⟨ <⁺★ , <⁻G (proj₂ (tangram-to x)) GT ⟩

tangram-from : ∀ {A B} → (A <:⁺ B × A <:⁻ B) → (A <: B)
tangram-from ⟨ <⁺ι , <⁻ι ⟩ = <ι
tangram-from ⟨ <⁺⇒ A′-A B+B′ , <⁻⇒ x x₁ ⟩ = <⇒ (tangram-from ⟨ x , A′-A ⟩) (tangram-from ⟨ B+B′ , x₁ ⟩)
tangram-from ⟨ <⁺★ , <⁻★ ⟩ = <★
tangram-from ⟨ <⁺★ , <⁻G <⁻ι y ⟩ = <G <ι y
tangram-from ⟨ <⁺★ , <⁻G <⁻★ y ⟩ = <★
tangram-from {A = A} ⟨ <⁺★ , <⁻G (<⁻⇒ x A-G) G-⇒ ⟩ = <G (<⇒ (tangram-from ⟨ x , <⁻★ ⟩ ) (tangram-from ⟨ <⁺★ , A-G ⟩)) G-⇒

tangram : ∀ {A B} → (A <: B) ⇔ (A <:⁺ B × A <:⁻ B)
tangram = record { to = tangram-to ; from = tangram-from }

tan-naive-to : ∀ {A B} → (A <:ₙ B) → (A <:⁺ B × B <:⁻ A)
tan-naive-to <ₙι = ⟨ <⁺ι , <⁻ι ⟩
tan-naive-to (<ₙ⇒ A<A B<B) = ⟨ (<⁺⇒ (proj₂ (tan-naive-to A<A)) (proj₁ (tan-naive-to B<B))) , (<⁻⇒ (proj₁ (tan-naive-to A<A)) (proj₂ (tan-naive-to B<B))) ⟩
tan-naive-to <ₙ★ = ⟨ <⁺★ , <⁻★ ⟩

tan-naive-from : ∀ {A B} → (A <:⁺ B × B <:⁻ A) → (A <:ₙ B)
tan-naive-from ⟨ <⁺ι , <⁻ι ⟩ = <ₙι
tan-naive-from ⟨ <⁺⇒ A′-A AB , <⁻⇒ A+A′ BA ⟩ = <ₙ⇒ (tan-naive-from ⟨ A+A′ , A′-A ⟩) (tan-naive-from ⟨ AB , BA ⟩)
tan-naive-from ⟨ <⁺★ , <⁻★ ⟩ = <ₙ★
tan-naive-from ⟨ <⁺★ , <⁻G BA x ⟩ = <ₙ★

tan-naive : ∀ {A B} → (A <:ₙ B) ⇔ (A <:⁺ B × B <:⁻ A)
tan-naive = record { to = tan-naive-to ; from = tan-naive-from }
```
