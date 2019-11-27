```
module Blame where
```

Here we give a formalisation of the blame calculus. We do this using the
_intrinsically-typed_ representation, where our types and terms are intertwined;
it makes no sense to define a term without a type. This fact gives rise to the
structure of this essay; we first define types and then later the terms.

## Imports

```
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax; ∃!) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _≟_) -- for Blame labels
open import Relation.Nullary using (¬_; Dec; yes; no)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong₂; sym)

open import Iff using (_⇔_)
```

## Types

Here we begin the formal development of the system. As mentioned before, we
first introduce types;

```
infixr 7 _⇒_

data Type : Set where
  ι : Type
  ★ : Type
  _⇒_ : Type → Type → Type

```

ι here is the `base` type; this is the tpye of any underlying type in the
metalanguage. This is exactly like the way that Agda defines the natural
numbers, using the Haskell implementation (recall that Agda is implemented in
Haskell; thus its _metalanguage_ is Haskell.)

★ is the dynamic type. Recall that the blame calculus is about casting types;
the dynamic type is the type that other types tend to be casted to.

_⇒_ is just the implication type that we are familiar with. 


### Ground types

```
data GType : Type → Set where
  G-ι :
    -------
    GType ι

  G-⇒ :
    -------------
    GType (★ ⇒ ★)
```

Ground types are a subset of types, encoding that a type can be the dynmaic type
if and only if it is either ι or ★ ⇒ ★.


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
```

That two types A and B are compatible means that we can safely cast from A to B.
This occurs if they are both the same base type ι, one of them is the dynamic
type ★, or they are both function types with compatible domains and ranges.

```
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

`ground-unique` and `ground-eq` embody two lemmas.

# Blame Labels

Here we introduce our _blame labels_. These are used to decorate casts,
essentially saying 'this label caused this cast to happen.' This is useful when
finding the source of erroneous computation; we can say at precisely which point
the casting went wrong.


We have here a shallow embedding of our blame labels. Ideally, we wanted to put
them in their own datatype, like this;

``
data Blame : Set where
  `_ : String → Blame
  not : Blame → Blame
``

However this does not exactly satisfy the requirements, as it does not contain
involution. So we tried parametrising it with an extra type which tells us if
the blame is positive or negative, like so;

``
data BType where
  + : BType
  - : BType

flip : BType → BType
flip + = -
flip - = +

data Blame : BType → Set where
  `_ : String → BType → Blame
  not : ∀ {t} → Blame t → Blame (flip t)
``

However this again was not satisfactory. We could not show Agda that `(flip .
flip) == id`, so it would not typecheck the type `not-inv : ∀ {B} not (not B) ≡
B`.

In the end we went for the definition below. We see that this is isomorphic to
the above, as `String * 2 ≡ String + String`. In this case, inj₁ indicates that
the blame is positive whilst inj₂ indicates that the blame is negative.

```
Blame : Set
Blame = String ⊎ String

`b_ : String → Blame
`b st = inj₁ st

not : Blame → Blame
not (inj₁ st) = inj₂ st
not (inj₂ st) = inj₁ st

not-inv : ∀ (B) → not (not B) ≡ B
not-inv (inj₁ x) = refl
not-inv (inj₂ y) = refl
```

`b constructs a positive blame label, whilst not flips the polarity of a blame
label by moving the string to the other side of the or.

## Subtypes

Here we define all four of the subtyping relations.

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

Four subtyping relations seems very excessive. However each serves a different
purpose.

The first, A <: B, means that cast from A to B never causes blame.

A <:⁺ B means that a cast from A to B never causes _positive_ blame. Recall that
positive blame means that the fault - that is, the incompatible cast - is the
cause of the term being cast at that instance.

A <:⁻ B means that a cast from A to B never causes _negative_ blame. Recall that
a cast causing negative blame (`not `p`) means that it assigns blame to the environment,
but not ``p`.

A <:ₙ B means that type A is more precise by type B. More precise here means
that A has less instances of the dynamic type than B. 


```
data Cast : Type → Type → Blame → Set where
  cast : ∀ (A B P) → Cast A B P

data safe : ∀ {A B} {P : Blame} → Cast A B P → Blame → Set where
  <+ : ∀ {A B} (P Q : Blame)
    → A <:⁺ B
      ----------
    → safe (cast A B P) Q

  <- : ∀ {A B P}
    → A <:⁻ B
      ----------------
    → safe (cast A B P) (P)

  <≢ : ∀ {A B} {P Q : Blame}
    → P ≢ Q
    → not P ≢ Q
      ----------
    → safe (cast A B P) Q
```

`safe (cast A B P) Q` is a witness to the fact that the cast A ⇒ B decorated by
P is safe for Q; that is, the evaluation of such a cast will never allocate
blame to Q.

The three constructors embody that;
- If A is a positive subtype of B, the cast will never allocate positive blame;
- If A is a negative subtype of B, the cast will never allocate negative blame;
- If A is more precise than B, then the cast will never allocate blame to any
  label that isn't P or not P.



## Tangram Lemma

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

tan-naive-to : ∀ {A B} → (A <:ₙ B) → (A <:⁺ B × B <:⁻ A)
tan-naive-to <ₙι = ⟨ <⁺ι , <⁻ι ⟩
tan-naive-to (<ₙ⇒ A<A B<B) = ⟨ (<⁺⇒ (proj₂ (tan-naive-to A<A)) (proj₁ (tan-naive-to B<B))) , (<⁻⇒ (proj₁ (tan-naive-to A<A)) (proj₂ (tan-naive-to B<B))) ⟩
tan-naive-to <ₙ★ = ⟨ <⁺★ , <⁻★ ⟩

tan-naive-from : ∀ {A B} → (A <:⁺ B × B <:⁻ A) → (A <:ₙ B)
tan-naive-from ⟨ <⁺ι , <⁻ι ⟩ = <ₙι
tan-naive-from ⟨ <⁺⇒ A′-A AB , <⁻⇒ A+A′ BA ⟩ = <ₙ⇒ (tan-naive-from ⟨ A+A′ , A′-A ⟩) (tan-naive-from ⟨ AB , BA ⟩)
tan-naive-from ⟨ <⁺★ , <⁻★ ⟩ = <ₙ★
tan-naive-from ⟨ <⁺★ , <⁻G BA x ⟩ = <ₙ★

tangram : ∀ {A B} → (A <: B) ⇔ (A <:⁺ B × A <:⁻ B)
tangram = record { to = tangram-to ; from = tangram-from }

tan-naive : ∀ {A B} → (A <:ₙ B) ⇔ (A <:⁺ B × B <:⁻ A)
tan-naive = record { to = tan-naive-to ; from = tan-naive-from }
```

It is easy to see the similarities between the different subtyping relations by
just observing the roles. The two above lemmas formalise that normal subtyping
can be reduced to positive and negative subtyping, whilst the second shows us
that naive subtyping can be assembled from positive subtyping and contravariant
negative subtyping.


## Terms

We first need to define contexts.

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

These are just the same as the De Bruijn in the textbook.

Now we can finally formalise terms!

```
infix  4 _⊢_
infix  5 ƛ_∙_
infixr 7 _·_
infix  8 blame
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

  ƛ_∙_  : ∀ {Γ B} (A)
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

```

Up to here the terms have all been as standard. Note that lambda expressions are
labelled with the type of the binding variable. 

```

  blame  : ∀ {Γ A}
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

Above we have the two new cases. The first constructor states that the term
blaming a blame label for something that has gone wrong can have any type. The
second states that a cast from a term of type A to a term of type B has overall
type B. Note that the constructor for cast requires as input proof that A is
compatible with B.

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
      -----------------------
    → Value (cast V P comp)

  V-★ : ∀ {Γ G}  {P : Blame} {V : Γ ⊢ G}
    → Value V
    → GType G
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
    → Value W
      ----------------------------------------------------
    → (cast V P (C-Step A∼A′ B∼B′)) · W —→
           cast (V · (cast W (not P) (∼-sym A∼A′))) P (B∼B′)

  ★★ : ∀ {Γ} {P : Blame} {V : Γ ⊢ ★} {C : ★ ∼ ★}
    → Value V
      -------------------
    → cast V P C —→ V

  A* : ∀ {Γ A G}  {P : Blame} {V : Γ ⊢ A}
    → Value V
    → GType G
    → (ug : unique-grounding A G)
      ----------------------------------------------------------
    → cast V P (C-A-★ A) —→ cast (cast V P (A∼G ug)) P (C-A-★ G)

  *A : ∀ {Γ A G} {P : Blame} {V : Γ ⊢ ★}
    → Value V
    → GType G
    → (ug : unique-grounding A G)
      ------------------------------------------------------------------
    → cast V P (C-★-B A) —→ cast (cast V P (C-★-B G)) P (∼-sym (A∼G ug))

  G★G : ∀ {Γ G}  {P Q : Blame} {V : Γ ⊢ G}
    → Value V
    → GType G
      -----------------------------------------------
    → cast (cast V P (C-A-★ G)) Q (C-★-B G) —→ V

  G★H : ∀ {Γ G H} {P Q : Blame} {V : Γ ⊢ G}
    → Value V
    → GType G
    → GType H
    → G ≢ H
      -----------------------------------------------
    → cast (cast V P (C-A-★ G)) Q (C-★-B H) —→ blame Q

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      --------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  ξ-cast : ∀ {Γ A B} {P : Blame} (A∼B : A ∼ B) {M M′ : Γ ⊢ A}
    → M —→ M′
    -------------------------------
    → cast M P A∼B —→ cast M′ P A∼B

  B-·₁ : ∀ {Γ A B} {P : Blame} {M : Γ ⊢ A}
    ------------------------------------------------------------------
    → ((blame {Γ = Γ} {A = A ⇒ B} P) · M) —→ (blame {Γ = Γ} {A = B} P)

  B-·₂ : ∀ {Γ A B} {P : Blame} {V : Γ ⊢ A ⇒ B}
    → Value V
    --------------------------
    → V · (blame P) —→ blame P

  B-cast : ∀ {Γ A B P Q} {A∼B : A ∼ B}
    -----------------------------------------------------------------
    → cast (blame {Γ = Γ} {A = A} P) Q A∼B —→ blame {Γ = Γ} {A = B} P


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
fail-ground : ∀ {A A′} → (A ⇒ A′ ∼ ★ ⇒ ★) → GType (★ ⇒ ★) → GType (A ⇒ A′)
fail-ground (C-Step (C-A-★ A) x₁) G-⇒ = {!!}
fail-ground (C-Step (C-★-B .★) (C-A-★ A)) G-⇒ = {!!}
fail-ground (C-Step (C-★-B .★) (C-★-B .★)) G-⇒ = G-⇒

failure : ∀ {Γ} (A B G H : Type) (V : Γ ⊢ A) (P Q R T U : Blame) {VV : Value V} {GG : GType G} {GH : GType H} (A≢★ : A ≢ ★) (A∼G : A ∼ G) (G≠H : G ≢ H)
  → cast (cast (cast (cast (cast V P A∼G) Q (C-A-★ G)) R (C-★-B H)) T (C-A-★ H)) U (C-★-B B) —↠ blame R
-- in this case, A = ι and B = ι 
failure ι B ι H V P Q R T U {VV} {GG} {GH} A≢★ C-ι G≢H = 
  begin
    cast (cast (cast (cast (cast V P C-ι) Q (C-A-★ ι)) R (C-★-B H)) T (C-A-★ H)) U (C-★-B B)
  —→⟨ ξ-cast (C-★-B B)
        (ξ-cast (C-A-★ H) (ξ-cast (C-★-B H) (ξ-cast (C-A-★ ι) (ιι VV)))) ⟩
    cast (cast (cast (cast V Q (C-A-★ ι)) R (C-★-B H)) T (C-A-★ H)) U (C-★-B B)
  —→⟨ ξ-cast (C-★-B B) (ξ-cast (C-A-★ H) (G★H VV GG GH G≢H)) ⟩
    cast (cast (blame R) T ((C-A-★ H))) U (C-★-B B)
  —→⟨ ξ-cast (C-★-B B) B-cast ⟩
    cast (blame R) U (C-★-B B)
  —→⟨ B-cast ⟩
    blame R
  ∎
failure ★ B G H V P Q R T U {VV} {GG} {GH} A≢★ (C-★-B G) G≢H = ⊥-elim (A≢★ refl)

failure (A ⇒ A′) B (★ ⇒ ★) H V P Q R T U {VV} {C-⇒} {G-⇒} A≢★ (C-Step A∼G A′∼G′) G≢H = ⊥-elim (G≢H refl)
-- failure (A ⇒ A′) B (★ ⇒ ★) ι N P Q R T U {VV} {C-⇒} {G-ι} A≢★ (C-Step (C-A-★ .A) A′∼G′) G≢H =
--   {!!}
--     —→⟨ {!!} ⟩
--   {!!}
-- failure (.★ ⇒ A′) B (★ ⇒ ★) ι N P Q R T U {VV} {C-⇒} {G-ι} A≢★ (C-Step (C-★-B .★) A′∼G′) G≢H =
--    begin
--     cast (cast (cast (cast (cast N P (C-Step (C-★-B ★) A′∼G′)) Q (C-A-★ (★ ⇒ ★))) R (C-★-B ι)) T (C-A-★ ι)) U (C-★-B B)
--   —→⟨ ξ-cast (C-★-B B)
--           (ξ-cast (C-A-★ ι) (ξ-cast (C-★-B ι) {!!})) ⟩
--     cast (cast (cast (cast N Q (C-A-★ (★ ⇒ A′))) R (C-★-B ι)) T (C-A-★ ι)) U (C-★-B B)
--   —→⟨ ξ-cast (C-★-B B) (ξ-cast (C-A-★ ι) (G★H VV {!!} G-ι λ ())) ⟩
--     cast (cast (blame R) T ((C-A-★ ι))) U (C-★-B B)
--   —→⟨ ξ-cast (C-★-B B) B-cast ⟩
--     cast (blame R) U (C-★-B B)
--   —→⟨ B-cast ⟩
--     blame R
--   ∎

failure (A ⇒ A′) B (★ ⇒ ★) ι N P Q R T U {VV} {C-⇒} {G-ι} A≢★ (C-Step A∼G A′∼G′) G≢H =
   begin
    cast (cast (cast (cast (cast N P (C-Step A∼G A′∼G′)) Q (C-A-★ (★ ⇒ ★))) R (C-★-B ι)) T (C-A-★ ι)) U (C-★-B B)
  —→⟨ ξ-cast (C-★-B B)
          (ξ-cast (C-A-★ ι) (ξ-cast (C-★-B ι) {!()!})) ⟩
    cast (cast (cast (cast N Q (C-A-★ (A ⇒ A′))) R (C-★-B ι)) T (C-A-★ ι)) U (C-★-B B)
  —→⟨ ξ-cast (C-★-B B) (ξ-cast (C-A-★ ι) (G★H VV {!!} G-ι λ ())) ⟩
    cast (cast (blame R) T ((C-A-★ ι))) U (C-★-B B)
  —→⟨ ξ-cast (C-★-B B) B-cast ⟩
    cast (blame R) U (C-★-B B)
  —→⟨ B-cast ⟩
    blame R
  ∎
-- failure (A ⇒ A′) B (★ ⇒ ★) H V P Q R T U {VV} {C-⇒} {G-ι} A≢★ (C-Step A∼G A′∼G′) G≢H =
--    begin
--     cast (cast (cast (cast (cast V P (C-Step A∼G A′∼G′)) Q (C-A-★ (★ ⇒ ★))) R (C-★-B H)) T (C-A-★ H)) U (C-★-B B)
--   —→⟨ ξ-cast (C-★-B B)
--           (ξ-cast (C-A-★ H) (ξ-cast (C-★-B H) {!ξ-cast ? ?!})) ⟩
--     cast (cast (cast (cast V Q (C-A-★ (A ⇒ A′))) R (C-★-B H)) T (C-A-★ H)) U (C-★-B B)
--   —→⟨ ξ-cast (C-★-B B) (ξ-cast (C-A-★ H) (G★H VV {!!} G-ι {!!})) ⟩
--     cast (cast (blame R) T ((C-A-★ H))) U (C-★-B B)
--   —→⟨ ξ-cast (C-★-B B) B-cast ⟩
--     cast (blame R) U (C-★-B B)
--   —→⟨ B-cast ⟩
--     blame R
--   ∎


  --  begin
  --   cast (cast (cast (cast (cast V P (C-Step A∼G A′∼G′)) Q (C-A-★ (★ ⇒ ★))) R (C-★-B H)) T (C-A-★ H)) U (C-★-B B)
  -- —→⟨ ξ-cast (C-★-B B)
  --         (ξ-cast (C-A-★ H) (ξ-cast (C-★-B H) {!ξ-cast ? ?!})) ⟩
  --   cast (cast (cast (cast V Q (C-A-★ (A ⇒ A′))) R (C-★-B H)) T (C-A-★ H)) U (C-★-B B)
  -- —→⟨ ξ-cast (C-★-B B) (ξ-cast (C-A-★ H) (G★H VV {!!} GH {!!})) ⟩
  --   cast (cast (blame R) T ((C-A-★ H))) U (C-★-B B)
  -- —→⟨ ξ-cast (C-★-B B) B-cast ⟩
  --   cast (blame R) U (C-★-B B)
  -- —→⟨ B-cast ⟩
  --   blame R
  -- ∎
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


∼ι→≡ι★ : ∀ {A} → A ∼ ι → A ≡ ι ⊎ A ≡ ★
∼ι→≡ι★ C-ι =  inj₁ refl
∼ι→≡ι★ (C-★-B .ι) = inj₂ refl

blame-doesnt-reduce : ∀ {Γ A P} {T : Γ ⊢ A} → ¬ (blame P —→ T)
blame-doesnt-reduce ()

blame-isnt-value : ∀ {Γ A P} → ¬ (Value {Γ = Γ} {A = A} (blame P))
blame-isnt-value ()

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y : A} {u v : B} {t s : C} → x ≡ y → u ≡ v → t ≡ s → f x u t ≡ f y v s
cong₃ f refl refl refl = refl

V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-⇒ v) (ξ-cast _ x) = V¬—→ v x
V¬—→ (V-★ V _) (ξ-cast _ x) = V¬—→ V x
V¬—→ (V-★ V GT′) (A* V′ G record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = A≢G (ground-to GT′ GT A∼G)

determinism : ∀ {Γ A} {M : Γ ⊢ A} {N L : Γ ⊢ A} → M —→ N → M —→ L → N ≡ L
determinism (β-ƛ x) (β-ƛ x₁) = refl
determinism (β-ƛ V) (ξ-·₂ _ M—→M′) = ⊥-elim (V¬—→ V M—→M′)
determinism (β-ƛ V) (ξ-·₁ red) = ⊥-elim (V¬—→ V-ƛ red)
determinism (β-ƛ x) (B-·₂ x₁) = ⊥-elim (blame-isnt-value x)

determinism (ιι _) (ιι _) = refl
determinism (ιι V-k) (ξ-cast c ML) = ⊥-elim (V¬—→ V-k ML)
determinism (ιι x) B-cast = refl

determinism (wrap _ _) (wrap _ _) = refl
determinism (wrap V W) (ξ-·₁ ML) = ⊥-elim (V¬—→ (V-⇒ V) ML )
determinism (wrap V W) (ξ-·₂ VC ML) = ⊥-elim (V¬—→ W ML)
determinism (wrap x W) (B-·₂ VB) = ⊥-elim (blame-isnt-value W)

determinism (★★ x) (★★ x₁) = refl
determinism (★★ x) (A* x₁ G record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢★ refl)
determinism (★★ x) (*A x₁ x₂ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢★ refl)
determinism (★★ V) (ξ-cast (C-A-★ ★) ML) = ⊥-elim (V¬—→ V ML)
determinism (★★ V) (ξ-cast (C-★-B ★) NM) = ⊥-elim (V¬—→ V NM)
determinism (★★ x) B-cast = refl

determinism (A* x G record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) (★★ V) = ⊥-elim (A≢★ refl)
determinism (A* V G ug) (ξ-cast (C-A-★ A) ML) = ⊥-elim (V¬—→ V ML)
determinism (A* x x₁ ug) B-cast = ⊥-elim (blame-isnt-value x)
determinism (A* x G-ι record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G })
            (A* x₂ x₃ ug) = ⊥-elim (case-⊎ (λ x₁ → A≢G x₁) (λ x₁ → A≢★ x₁) (∼ι→≡ι★ A∼G))
determinism (A* x G-⇒ ug) (A* x₂ G-ι record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G })
            = ⊥-elim (case-⊎ (λ x₁ → A≢G x₁) (λ x₁ → A≢★ x₁) (∼ι→≡ι★ A∼G))
determinism (A* _ G-⇒ record { GT = GT₁ ; A≢★ = A≢★₁ ; A≢G = A≢G₁ ; A∼G = (C-★-B .(★ ⇒ ★)) })
            (A* _ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = (C-★-B .(★ ⇒ ★)) }) = refl
determinism (A* _ G-⇒ record { GT = GT₁ ; A≢★ = A≢★₁ ; A≢G = A≢G₁ ; A∼G = (C-Step (C-A-★ A) (C-A-★ A₁)) })
            (A* _ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = (C-Step (C-A-★ A) (C-A-★ A₁)) }) = refl
determinism (A* _ G-⇒ record { GT = GT₁ ; A≢★ = A≢★₁ ; A≢G = A≢G₁ ; A∼G = (C-Step (C-A-★ A) (C-A-★ ★)) })
            (A* _ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = (C-Step (C-A-★ A) (C-★-B ★)) }) = {!refl!}
determinism (A* _ G-⇒ record { GT = GT₁ ; A≢★ = A≢★₁ ; A≢G = A≢G₁ ; A∼G = (C-Step (C-A-★ A) (C-★-B .★)) })
            (A* _ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = (C-Step (C-A-★ .A) A∼G₃) }) = {!!}
determinism (A* _ G-⇒ record { GT = GT₁ ; A≢★ = A≢★₁ ; A≢G = A≢G₁ ; A∼G = (C-Step (C-A-★ .★) A∼G₂) })
            (A* _ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = (C-Step (C-★-B .★) A∼G₃) }) = {!!}
determinism (A* _ G-⇒ record { GT = GT₁ ; A≢★ = A≢★₁ ; A≢G = A≢G₁ ; A∼G = (C-Step (C-★-B .★) A∼G₂) })
            (A* _ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = {!!}

determinism (*A _ G-ι record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) (G★G _ G-ι) = ⊥-elim (A≢G refl)
determinism (*A _ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) (G★G _ G-⇒) = ⊥-elim (A≢G refl)
determinism (*A V G ug) (ξ-cast _ ML) = ⊥-elim (V¬—→ V ML)

determinism (*A V G-ι record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G })
            (*A VV G ug) = ⊥-elim (case-⊎ (λ x → A≢G x) (λ x → A≢★ x) (∼ι→≡ι★ A∼G))
determinism (*A V G-⇒ ug) (*A VV GG ug₁) = {!!}

determinism MN@(G★G V G) ML@(*A VV GG ug) = sym (determinism ML MN)
determinism (G★G x _) (G★G x₁ _) = refl
determinism (G★G V _) (G★H V′ _ _ A≢A ) = ⊥-elim (A≢A refl)
determinism (G★G V G) (ξ-cast (C-★-B B) ML) = ⊥-elim (V¬—→ (V-★ V G) ML)

determinism (G★H V G G-ι G≢A) (*A x₂ G-ι record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢G refl)
determinism (G★H V G G-⇒ G≢A) (*A x₂ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢G refl)
determinism (G★H _ _ _ A≢A) (G★G _ _) = ⊥-elim (A≢A refl)
determinism (G★H _ _ _ _) (G★H _ _ _ _) = refl
determinism (G★H V G H _) (ξ-cast _ ML) = ⊥-elim (V¬—→ (V-★ V G) ML )

determinism (ξ-·₁ MN) (wrap V W) = ⊥-elim (V¬—→ (V-⇒ V) MN)
determinism (ξ-·₁ MN) (ξ-·₁ ML) = cong₂ _·_ (determinism MN ML) refl
determinism (ξ-·₁ MN) (ξ-·₂ V ML) = ⊥-elim (V¬—→ V MN)
determinism (ξ-·₁ MN) (B-·₂ V) = ⊥-elim (V¬—→ V MN)
determinism (ξ-·₁ x) (β-ƛ x₁) = ⊥-elim (V¬—→ V-ƛ x)
determinism (ξ-·₁ x) B-·₁ = ⊥-elim (blame-doesnt-reduce x)

determinism (ξ-·₂ _ MN) (β-ƛ V) = ⊥-elim (V¬—→ V MN)
determinism (ξ-·₂ V2 MN) (wrap V W) = ⊥-elim (V¬—→ W MN)
determinism (ξ-·₂ V MN) (ξ-·₁ ML) = ⊥-elim (V¬—→ V ML)
determinism (ξ-·₂ V MN) (ξ-·₂ x₁ ML) = cong₂ _·_ refl (determinism MN ML)
determinism (ξ-·₂ x x₁) B-·₁ = ⊥-elim (blame-isnt-value x)
determinism (ξ-·₂ _ BM) (B-·₂ _) = ⊥-elim (blame-doesnt-reduce BM)

determinism (ξ-cast _ MN) (ιι V) = ⊥-elim (V¬—→ V MN)
determinism (ξ-cast _ MN) (★★ V) = ⊥-elim (V¬—→ V MN )
determinism (ξ-cast _ MN) (A* V _ ug) = ⊥-elim (V¬—→ V MN)
determinism (ξ-cast _ MN) (*A V _ ug) = ⊥-elim (V¬—→ V MN)
determinism (ξ-cast _ MN) (G★G V G) = ⊥-elim (V¬—→ (V-★ V G) MN)
determinism (ξ-cast _ MN) (G★H V G H _) = ⊥-elim (V¬—→ (V-★ V G) MN)
determinism (ξ-cast C MN) (ξ-cast .C ML) = cong₃ cast (determinism MN ML) refl refl
-- determinism (ξ-cast A∼B x) B-cast = ⊥-elim (blame-doesnt-reduce x)

determinism B-·₁ B-·₁ = refl

determinism (B-·₂ V) (ξ-·₁ ML) = ⊥-elim (V¬—→ V ML )
determinism (B-·₂ x) (B-·₂ x₁) = refl
determinism (B-·₂ x) (β-ƛ x₁) = ⊥-elim (blame-isnt-value x₁)
determinism (B-·₂ x) (ξ-·₂ x₁ y) = ⊥-elim (blame-doesnt-reduce y)
determinism (B-·₂ x) (B-·₁) = ⊥-elim (blame-isnt-value x)

determinism (B-cast) (B-cast) = refl
determinism B-cast (ιι x) = refl
determinism B-cast (★★ x) = refl
determinism B-cast (A* x x₁ ug) = ⊥-elim (blame-isnt-value x)
determinism B-cast (*A x x₁ ug) = ⊥-elim (blame-isnt-value x)
-- determinism B-cast (ξ-cast A∼B y) = ⊥-elim (blame-doesnt-reduce y)

-- repeated cases
determinism (*A x G record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) (★★ x₁) = ⊥-elim (A≢★ refl)
determinism (*A x₂ G-ι record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) (G★H V G G-ι G≢A) = ⊥-elim (A≢G refl)
determinism (*A x₂ G-⇒ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) (G★H V G G-⇒ G≢A) = ⊥-elim (A≢G refl)
determinism (B-·₂ VB) (wrap x W) = ⊥-elim (blame-isnt-value W) --determinism {!!} ((B-·₂ x₁))


Progress
data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

  blame :
      (P : Blame)
    → (M ≡ blame P)
    → Progress M

A⇒B∼★⇒★ : ∀ (A B) → A ⇒ B ∼ ★ ⇒ ★
A⇒B∼★⇒★ A B = C-Step (C-A-★ A) (C-A-★ B)


progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M
progress (k x) = done V-k
progress (` ())
progress (ƛ A ∙ T) = done V-ƛ
progress {A} (L · M) with progress L
... | step L→L′ = step (ξ-·₁ L→L′)
progress {A} (blame P₁ · M) | blame P eq = step B-·₁
progress ((ƛ A ∙ L) · M) | done V-ƛ with progress M
...      | step M→M′ = step (ξ-·₂ V-ƛ M→M′)
...      | done VM = step (β-ƛ VM)
progress {_} ((ƛ A ∙ L) · blame P) | done V-ƛ | blame p eq = step (B-·₂ V-ƛ)
progress ((cast A B (C-Step C C₁)) · M) | done (V-⇒ x) with progress M
...      | step M→M′ = step (ξ-·₂ (V-⇒ x) M→M′)
...      | done VM = step (wrap x VM)
progress {_} (cast A B (C-Step C C₁) · blame P) | done (V-⇒ x) | blame p eq = step (B-·₂ (V-⇒ x))
progress (blame P) = blame P refl
progress (cast T Q x) with progress T
... | step T→T′ = step (ξ-cast x T→T′)
progress (cast (blame P₁) Q x) | blame P eq = step B-cast 
progress (cast T Q C-ι) | done VT = step (ιι VT)

progress (cast (k _) Q (C-A-★ ι)) | done V-k = done (V-★ V-k G-ι)
progress (cast T Q (C-A-★ ★)) | done VT = step (★★ VT)

progress (cast _ _ (C-A-★ (★ ⇒ ★))) | done V = done (V-★ V G-⇒)
progress (cast _ _ (C-A-★ (ι ⇒ B))) | done V = step (A* V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ ι B }))
progress (cast _ _ (C-A-★ (★ ⇒ ι))) | done V = step (A* V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ ★ ι }))
progress (cast _ _ (C-A-★ (★ ⇒ (A ⇒ B)))) | done V = step (A* V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ ★ (A ⇒ B) }))
progress (cast _ _ (C-A-★ ((A ⇒ A₁) ⇒ B))) | done V = step (A* V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ (A ⇒ A₁) B }))

progress (cast .(cast _ _ (C-A-★ ι)) Q (C-★-B ι)) | done (V-★ VT G-ι) = step (G★G VT G-ι )
progress (cast .(cast _ _ (C-A-★ (★ ⇒ ★))) Q (C-★-B ι)) | done (V-★ VT G-⇒) = step (G★H VT G-⇒ G-ι λ ())
progress (cast .(cast _ _ (C-A-★ ι)) Q (C-★-B (★ ⇒ ★))) | done (V-★ VT G-ι) = step (G★H VT G-ι G-⇒ λ ())
progress (cast .(cast _ _ (C-A-★ (★ ⇒ ★))) Q (C-★-B (★ ⇒ ★))) | done (V-★ VT G-⇒) = step (G★G VT G-⇒ )

progress (cast T Q (C-★-B ★)) | done VT = step (★★ VT)
progress (cast T Q (C-★-B (ι ⇒ B₁))) | done V = step (*A V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ ι B₁ }))
progress (cast T Q (C-★-B (★ ⇒ ι))) | done V = step (*A V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ ★ ι }))
progress (cast T Q (C-★-B (★ ⇒ B₁ ⇒ B₂))) | done V = step (*A V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ ★ (B₁ ⇒ B₂) }))
progress (cast T Q (C-★-B ((B ⇒ B₂) ⇒ B₁))) | done V = step (*A V G-⇒ (record { GT = G-⇒ ; A≢★ = λ () ; A≢G = λ () ; A∼G = A⇒B∼★⇒★ (B ⇒ B₂) B₁ }))

progress (cast T Q (C-Step x x₁)) | done VT = done (V-⇒ VT)

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

  -- safe-blame : ∀ {Γ A Q}
  --   → (P : Blame)
  --     -----------------------------
  --   → safe-term {Γ} {A} (blame P) Q

  safe-cast : ∀ {Γ A B Q} {M : Γ ⊢ A} {C : Cast A B Q}
    → (P : Blame)
    → safe-term M P
    → safe C P
    → (A∼B : A ∼ B)
      ---------------------------
    → safe-term (cast M Q A∼B) P


safe-subst : ∀ {Γ A B Q} {M : Γ , A ⊢ B} {N : Γ ⊢ A} → safe-term (ƛ A ∙ M) Q → safe-term (N) Q → safe-term (M [ N ]) Q
safe-subst (safe-ƛ (safe-k P)) N = {!safe-k ?!}
safe-subst (safe-ƛ (safe-` x P)) N = {!!}
safe-subst (safe-ƛ (safe-ƛ M)) N = safe-ƛ {!!}
safe-subst (safe-ƛ (safe-· M N)) V = safe-· {!!} {!!}
-- safe-subst (safe-ƛ (safe-blame P)) N = safe-blame P
safe-subst (safe-ƛ (safe-cast P M x A∼B)) N = safe-cast P {!!} x A∼B

blame-is-unsafe : ∀ {Γ A P Q} → ¬ (safe-term {Γ = Γ} {A = A} (blame Q) P)
blame-is-unsafe ()

tick-not-val : ∀ {Γ A x} → ¬ (Value {Γ = Γ} {A = A} (` x))
tick-not-val ()

not-blame : ∀ {Γ A} {Q : Blame} {M : Γ ⊢ A} → safe-term M Q → ¬ ( M —→ blame Q )
not-blame (safe-· (safe-` x P) st₁) (B-·₂ V) = tick-not-val V
not-blame (safe-· (safe-ƛ st) st₁) red = {!!}
not-blame (safe-· (safe-· st st₂) st₁) (B-·₂ ())
not-blame (safe-· (safe-cast P STM x₂ A∼B) ()) (B-·₂ _)

not-blame (safe-cast P st x (C-★-B .ι)) (G★H VV G-ι G-ι G≢B) = (G≢B refl)
not-blame (safe-cast P st (<≢ x x₁) (C-★-B .ι)) (G★H V-ƛ G-⇒ G-ι G≢B) = x refl
not-blame (safe-cast P st (<≢ x x₁) (C-★-B .ι)) (G★H (V-⇒ VV) G-⇒ G-ι G≢B) = x refl
not-blame (safe-cast P st (<≢ x x₁) (C-★-B .(★ ⇒ ★))) (G★H VV G-ι G-⇒ G≢B) = x refl
not-blame (safe-cast P st x (C-★-B .(★ ⇒ ★))) (G★H VV G-⇒ G-⇒ G≢B) = G≢B refl

not-blame (safe-cast P x (<- x₁) .(C-★-B (★ ⇒ ★))) (G★H V-k G-ι G-⇒ x₃) = {!!}
not-blame (safe-cast P x (<- x₁) .(C-★-B ι)) (G★H V-ƛ G-⇒ G-ι x₃) = {!!}
not-blame (safe-cast P x (<- x₁) .(C-★-B ι)) (G★H (V-⇒ x₂) G-⇒ G-ι x₃) = {!!}

blame-safety : ∀ {Γ A} {P : Blame} {M N : Γ ⊢ A} → safe-term M P → M —→ N → safe-term N P
blame-safety (safe-· x y) (β-ƛ x₁) = {!!}


blame-safety (safe-· (safe-cast P SV x (C-Step A∼A′ B∼B′)) SN) (wrap VV VN) = safe-cast P (safe-· SV (safe-cast P SN (<+ {!_!} _ {!!}) (∼-sym A∼A′))) (<+ _ _ {!!}) B∼B′

-- blame-safety (safe-· (safe-cast P SV x (C-Step C-ι B∼B′)) SN) (wrap VV VN) = safe-cast P (safe-· SV (safe-cast P SN {!!} (∼-sym C-ι))) (<+ _ _ {!!}) B∼B′
-- blame-safety (safe-· (safe-cast P SV x (C-Step (C-A-★ A) B∼B′)) SN) (wrap VV VN) = safe-cast P (safe-· SV (safe-cast P SN {!!} (∼-sym (C-A-★ A)))) (<+ _ _ {!!}) B∼B′
-- blame-safety (safe-· (safe-cast P SV x (C-Step (C-★-B B) B∼B′)) SN) (wrap VV VN) = safe-cast P (safe-· SV (safe-cast P SN {!!} (∼-sym (C-★-B B)))) (<+ _ _ {!!}) B∼B′
-- blame-safety (safe-· (safe-cast P SV x (C-Step (C-Step A∼A′ A∼A′₁) B∼B′)) SN) (wrap VV VN) = safe-cast P (safe-· SV (safe-cast P SN {!!} (∼-sym (C-Step A∼A′ A∼A′₁)))) (<+ _ _ {!!}) B∼B′

blame-safety (safe-· M N) (ξ-·₁ red) = safe-· (blame-safety M red) N
blame-safety (safe-· M N) (ξ-·₂ x red) = safe-· M (blame-safety  N red)

blame-safety (safe-cast p st x C-ι) (ιι x₁) = st
blame-safety (safe-cast p st x (C-A-★ ★)) (★★ x₁) = st

blame-safety (safe-cast p st x (C-A-★ ι)) (A* x₁ _ record { GT = G-ι ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢G refl)
blame-safety (safe-cast p st x (C-A-★ ★)) (A* x₁ _ record { GT = G-ι ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢★ refl)
blame-safety (safe-cast p st x (C-A-★ ★)) (A* x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢★ refl)
blame-safety (safe-cast p st x (C-A-★ (A ⇒ A₁))) (A* x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G })
    = safe-cast p (safe-cast p st (<+ _ _ (<⁺⇒ <⁻★ <⁺★)) A∼G) (<+ _ _ <⁺★) (C-A-★ (★ ⇒ ★))

blame-safety (safe-cast p st x (C-★-B ι)) (*A x₁ _ record { GT = G-ι ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢G refl)
blame-safety (safe-cast p st x (C-★-B ★)) (*A x₁ _ record { GT = GT ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = ⊥-elim (A≢★ refl)
-- blame-safety (safe-cast p st x (C-★-B (ι ⇒ ι))) (*A x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) -- = -- safe-cast {!!} (safe-cast {!!} st {!!} (C-★-B (★ ⇒ ★))) (<+ _ _ (<⁺⇒ (<⁻G <⁻ι G-ι) {!!})) (∼-sym A∼G)
-- blame-safety (safe-cast p st x (C-★-B (ι ⇒ ★))) (*A x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = safe-cast {!!} (safe-cast {!!} st {!!} (C-★-B (★ ⇒ ★))) (<+ _ _ (<⁺⇒ (<⁻G <⁻ι G-ι) {!!})) (∼-sym A∼G)
-- blame-safety (safe-cast p st x (C-★-B (ι ⇒ C ⇒ C₁))) (*A x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = safe-cast {!!} (safe-cast {!!} st {!!} (C-★-B (★ ⇒ ★))) (<+ _ _ (<⁺⇒ (<⁻G <⁻ι G-ι) {!!})) (∼-sym A∼G)
-- blame-safety (safe-cast p st x (C-★-B (★ ⇒ C))) (*A x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = safe-cast {!!} (safe-cast {!!} st {!!} (C-★-B (★ ⇒ ★))) (<+ _ _ (<⁺⇒ {!!} {!!})) (∼-sym A∼G)
-- blame-safety (safe-cast p st x (C-★-B ((B ⇒ B₁) ⇒ C))) (*A x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = A∼G }) = safe-cast {!!} (safe-cast {!!} st {!!} (C-★-B (★ ⇒ ★))) (<+ _ _ (<⁺⇒ {!!} {!!})) (∼-sym A∼G)
blame-safety (safe-cast p st x (C-★-B (B ⇒ C))) (*A x₁ _ record { GT = G-⇒ ; A≢★ = A≢★ ; A≢G = A≢G ; A∼G = (C-Step A∼G₁ A∼G₂) }) = {!!}

blame-safety (safe-cast p st x (C-★-B .ι)) (G★G V-k T) = safe-k p
blame-safety (safe-cast p (safe-cast _ (safe-ƛ st) _ _) _ _) (G★G V-ƛ _) = safe-ƛ st
blame-safety (safe-cast p (safe-cast p (safe-cast p st x₂ A∼B) x₁ (C-A-★ (.★ ⇒ .★))) x (C-★-B (★ ⇒ ★))) (G★G (V-⇒ VN) T) = safe-cast p st (<+ _ _ (<⁺⇒ <⁻★ <⁺★)) A∼B

blame-safety (safe-cast P x x₁ (C-★-B ι)) (G★H x₂ G-ι x₄ x₅) = ⊥-elim (x₅ refl)
blame-safety (safe-cast P x x₁ (C-★-B (★ ⇒ ★))) (G★H x₂ G-⇒ G-⇒ x₅) = ⊥-elim (x₅ refl)
blame-safety (safe-cast P (safe-cast .P x x₃ .(C-A-★ (★ ⇒ ★))) x₁ (C-★-B ι)) (G★H x₂ G-⇒ G-ι x₅) = {!!}
blame-safety (safe-cast P x x₁ (C-★-B (B ⇒ B₁))) (G★H x₂ G-ι x₄ x₅) = {!!}

blame-safety (safe-cast P x x₁ (C-★-B ★)) (★★ x₂) = x

-- blame-safety (safe-cast P st SCP (C-★-B ι)) (G★H VV G-ι Gι G≢ι) = {!!} --  ⊥-elim (G≢ι refl)
-- blame-safety (safe-cast P (safe-cast .P (safe-ƛ st) x .(C-A-★ (★ ⇒ ★))) SCP (C-★-B ι)) (G★H V-ƛ G-⇒ Gι G≢ι) = {!!}
-- blame-safety (safe-cast P st SCP (C-★-B ι)) (G★H (V-⇒ VV) G-⇒ Gι G≢ι) = {!!}
-- blame-safety (safe-cast P x x₁ (C-★-B (.★ ⇒ .★))) (G★H x₂ x₃ G-⇒ x₅) = {!!}

-- blame-safety (safe-cast p st c t) (G★H {Q = Q} x₁ x₂ Y _) = safe-blame Q

blame-safety (safe-cast p st x A∼B) (ξ-cast A∼B′ red) = safe-cast p (blame-safety st red) x A∼B

-- blame-safety (safe-cast p (safe-blame P) x A∼B) B-cast = safe-blame P

```
