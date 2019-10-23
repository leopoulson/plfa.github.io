---
title     : "Assignment2: TSPL Assignment 2"
layout    : page
permalink : /TSPL/2019/Assignment2/
---

```
module Assignment2 where
```

## YOUR NAME AND EMAIL GOES HERE
Leo Poulson
s1983328@ed.ac.uk

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
```bash
submit tspl cw2 Assignment2.lagda.md
```
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).


## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality; ∀-extensionality)
open import plfa.part1.Negation using (assimilation)
open plfa.part1.Isomorphism.≃-Reasoning
```

## Equality


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


## Equality

#### Exercise `≤-Reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.

```
-- Your code goes here
```

## Isomorphism

#### Exercise `≃-implies-≲` (practice)

Show that every isomorphism implies an embedding.
```
-- postulate
--   ≃-implies-≲ : ∀ {A B : Set}
--     → A ≃ B
--       -----
--     → A ≲ B
```

```
≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ a≃b =
  record
    { to      = _≃_.to a≃b
    ; from    = _≃_.from a≃b
    ; from∘to = _≃_.from∘to a≃b }
-- Your code goes here
```

#### Exercise `_⇔_` (practice) {#iff}

Define equivalence of propositions (also known as "if and only if") as follows:
```
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
```
Show that equivalence is reflexive, symmetric, and transitive.

```
⇔-refl : ∀ {A : Set}
    ---
  → A ⇔ A
⇔-refl =
  record
    { to   = λ {x → x}
    ; from = λ {y → y}
    }

⇔-symm : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-symm A⇔B =
  record
    { to   = _⇔_.from A⇔B
    ; from = _⇔_.to A⇔B
    }

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to   = _⇔_.to   B⇔C ∘ _⇔_.to A⇔B
    ; from = _⇔_.from A⇔B ∘ _⇔_.from B⇔C
    }

```

#### Exercise `Bin-embedding` (stretch) {#Bin-embedding}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin) and
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to : ℕ → Bin
    from : Bin → ℕ

which satisfy the following property:

    from (to n) ≡ n

Using the above, establish that there is an embedding of `ℕ` into `Bin`.
```
-- Your code goes here
```

Why do `to` and `from` not form an isomorphism?

## Connectives

#### Exercise `⇔≃×` (recommended)

Show that `A ⇔ B` as defined [earlier]({{ site.baseurl }}/Isomorphism/#iff)
is isomorphic to `(A → B) × (B → A)`.

```
⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to      = λ x → ⟨ to x , from x ⟩
    ; from    = λ z → record { to = proj₁ z ; from = proj₂ z }
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    } where open _⇔_
```

#### Exercise `⊎-comm` (recommended)

Show sum is commutative up to isomorphism.

```
⊎-swap : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-swap a⊎b = case-⊎ inj₂ inj₁ a⊎b

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = ⊎-swap
    ; from    = ⊎-swap
    ; from∘to = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    }
```

#### Exercise `⊎-assoc` (practice)

Show sum is associative up to isomorphism.


```

⊎-l-assoc : ∀ {A B C : Set} → (A ⊎ B) → A ⊎ (B ⊎ C)
⊎-l-assoc (inj₁ x) = (inj₁ x)
⊎-l-assoc (inj₂ x) = inj₂ (inj₁ x)

⊎-r-assoc : ∀ {A B C : Set} → B ⊎ C → (A ⊎ B) ⊎ C
⊎-r-assoc (inj₁ x) = inj₁ (inj₂ x)
⊎-r-assoc (inj₂ x) = inj₂ x

```
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to   = λ { (inj₁ x) → ⊎-l-assoc x
               ; (inj₂ x) → inj₂ (inj₂ x) }
    ; from = λ { (inj₁ x) → inj₁ (inj₁ x)
               ; (inj₂ x) → ⊎-r-assoc x }
    ; from∘to = λ { (inj₁ x) → {!!}
                  ; (inj₂ x) → refl }
    ; to∘from = λ { (inj₁ x) → refl
                  ; (inj₂ x) → {!!} }
    }



#### Exercise `⊥-identityˡ` (recommended)

Show empty is the left identity of sums up to isomorphism.

```
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ { (inj₂ x) → x } -- no constructors for ⊥
    ; from = inj₂
    ; from∘to = λ { (inj₂ x) → refl }
    ; to∘from = λ y → refl
    }
```

#### Exercise `⊥-identityʳ` (practice)

Show empty is the right identity of sums up to isomorphism.

```
⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to = λ { (inj₁ x) → x }
    ; from = λ y → inj₁ y
    ; from∘to = λ { (inj₁ x) → refl }
    ; to∘from = λ y → refl
    }
```

#### Exercise `⊎-weak-×` (recommended)

Show that the following property holds:

postulate
  ⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)

This is called a _weak distributive law_. Give the corresponding
distributive law, and explain how it relates to the weak version.

```
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , snd ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , snd ⟩ = inj₂ ⟨ y , snd ⟩
```

The corresponding distributive law is as follows

⊎-distrib-× : ∀ {A B C : Set} → (A ⊎ B) × C ≃ A ⊎ (B × C)

Its relation to ⊎-weak-× is that in the record definition for ⊎-distrib-×,
⊎-weak-× would inhabit the `to` constructor.

#### Exercise `⊎×-implies-×⊎` (practice)

Show that a disjunct of conjuncts implies a conjunct of disjuncts:

postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)

Does the converse hold? If so, prove; if not, give a counterexample.

```
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ fst , snd ⟩) = ⟨ inj₁ fst , inj₁ snd ⟩
⊎×-implies-×⊎ (inj₂ ⟨ fst , snd ⟩) = ⟨ inj₂ fst , inj₂ snd ⟩
```


## Negation

#### Exercise `<-irreflexive` (recommended)

Using negation, show that
[strict inequality]({{ site.baseurl }}/Relations/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.

```
<-irreflexive : ∀ {n : ℕ} → ¬( n < n )
<-irreflexive (s<s n<n) = <-irreflexive n<n
```


#### Exercise `trichotomy` (practice)

Show that strict inequality satisfies
[trichotomy]({{ site.baseurl }}/Relations/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that not only one of the three must hold,
but that when one holds the negation of the other two must also hold.

```
-- Your code goes here
```

#### Exercise `⊎-dual-×` (recommended)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.

    ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

This result is an easy consequence of something we've proved previously.

```
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }


⊎-dual-× : ∀ {A B : Set} → (A ⊎ B → ⊥) ≃ ((A → ⊥) × (B → ⊥))
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {C = ⊥}
```

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, can you give a relation weaker than
isomorphism that relates the two sides?

We do not have that

  ¬ (A × B) → (¬ A) ⊎ (¬ B)

If we are given a function from (A × B) to ⊥, we have no way of knowing which of
A or B does not hold. So, we cannot give a function from A to ⊥ - because it may
be the case that A holds whilst B does not (respectively we cannot give a
function from B to ⊥).

However we do have the implication in the other direction;

```
⊎-dual-imp-× : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
⊎-dual-imp-× (inj₁ x) = λ z → x (proj₁ z)
⊎-dual-imp-× (inj₂ y) = λ z → y (proj₂ z)
```

#### Exercise `Classical` (stretch)

Consider the following principles:

  * Excluded Middle: `A ⊎ ¬ A`, for all `A`
  * Double Negation Elimination: `¬ ¬ A → A`, for all `A`
  * Peirce's Law: `((A → B) → A) → A`, for all `A` and `B`.
  * Implication as disjunction: `(A → B) → ¬ A ⊎ B`, for all `A` and `B`.
  * De Morgan: `¬ (¬ A × ¬ B) → A ⊎ B`, for all `A` and `B`.

Show that each of these implies all the others.

record AllClassical (A B : Set) : Set₁ where
  field
    em : A ⊎ ¬ A
    dne : ¬ ¬ A → A
    peirce : ((A → B) → A) → A
    impasdis : (A → B) → ¬ A ⊎ B
    demorgan : ¬ (¬ A × ¬ B) → A ⊎ B
-- Your code goes here

em-implies : ∀ {A B : Set} → (A ⊎ ¬ A) → AllClassical A B
em-implies (inj₁ a) =
  record
    { em = (inj₁ a)
    ; dne = λ _ → a
    ; peirce = λ _ → a
    ; impasdis = λ z → inj₂ (z a)
    ; demorgan = λ _ → inj₁ a }
em-implies (inj₂ ¬a) =
  record
    { em = (inj₂ ¬a)
    ; dne = λ ¬¬a → ⊥-elim (¬¬a ¬a)
    ; peirce = λ x → {!!}
    ; impasdis = λ _ → inj₁ ¬a
    ; demorgan = λ x → {!!}
    }

dne-implies : ∀ {A B : Set} → (¬ ¬ A → A) → AllClassical A B
dne-implies dne =
  record
    { em = inj₂ {!!}
    ; dne = dne
    ; peirce = {!!}
    ; impasdis = {!!}
    ; demorgan = {!!}
    }

```
em-imp-dne : ∀ {A : Set} → (A ⊎ ¬ A) → (¬ ¬ A → A)
em-imp-dne (inj₁ a) = λ _ → a
em-imp-dne (inj₂ ¬a) = λ ¬¬a → ⊥-elim (¬¬a ¬a)

dne-imp-peirce : ∀ {A B : Set} → (¬ ¬ A → A) → (((A → B) → A) → A)
dne-imp-peirce r = {!!}
```

#### Exercise `Stable` (stretch)

Say that a formula is _stable_ if double negation elimination holds for it:
```
Stable : Set → Set
Stable A = ¬ ¬ A → A
```
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.

```
neg-stable : ∀ {A : Set} → Stable (¬ A)
neg-stable = λ z z₁ → z (λ z₂ → z₂ z₁)

conj-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
conj-stable a b = λ ¬¬ab → ⟨ (a (λ ¬a → ¬¬ab (λ ab → ¬a (proj₁ ab)) )),
                             (b (λ ¬b → ¬¬ab (λ ab → ¬b (proj₂ ab)))) ⟩
```


## Quantifiers


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:

```
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ { f → ⟨ (λ x → proj₁ (f x) ) , (λ x → proj₂ (f x)) ⟩ }
    ; from = λ { ⟨ fl , fr ⟩ → λ x → ⟨ fl x , fr x ⟩ }
    ; from∘to = λ f → refl
    ; to∘from = λ { ⟨ fl , fr ⟩ → refl }
    }
```

Compare this with the result (`→-distrib-×`) in
Chapter [Connectives]({{ site.baseurl }}/Connectives/).

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

It's the same proof!

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
```
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ fb) = λ x → (inj₁ (fb x))
⊎∀-implies-∀⊎ (inj₂ fc) = λ x → (inj₂ (fc x))
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
```
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```

Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.

```
∀-× : ∀ {B : Tri → Set} →
  (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× =
  record
    { to = λ z → ⟨ z aa , ⟨ z bb , z cc ⟩ ⟩
    ; from = λ { ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ →
                   λ { aa → baa ; bb → bbb ; cc → bcc } }
    ; from∘to = λ {z → ∀-extensionality (
                   λ { aa → refl ; bb → refl ; cc → refl } ) }
    ; to∘from = λ { ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ → refl }
    }
```

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
```
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to   = λ { ⟨ x , (inj₁ b) ⟩ → inj₁ ⟨ x , b ⟩ ;
                 ⟨ x , (inj₂ c) ⟩ → inj₂ ⟨ x , c ⟩}
    ; from = λ { (inj₁ ⟨ x , b ⟩) → ⟨ x , inj₁ b ⟩ ;
                 (inj₂ ⟨ x , c ⟩) → ⟨ x , inj₂ c ⟩ }
    ; from∘to =  λ { ⟨ x , (inj₁ b) ⟩ → refl ;
                     ⟨ x , (inj₂ c) ⟩ → refl }
    ; to∘from = λ { (inj₁ ⟨ x , b ⟩) → refl ;
                    (inj₂ ⟨ x , c ⟩) → refl }
    }
```


#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
```
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ bx , cx ⟩ ⟩ = ⟨ ⟨ x , bx ⟩ , ⟨ x , cx ⟩ ⟩
```
Does the converse hold? If so, prove; if not, explain why.

×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
  (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)

This does not hold; the two xs may be different xs, so we have no proof that
there exists one x such that B and C hold for it.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.

```
∃-⊎ : ∀ {B : Tri → Set} →
  (∃[ x ] B x) ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
    { to = λ { ⟨ aa , bx ⟩ → inj₁ bx ;
               ⟨ bb , bx ⟩ → inj₂ (inj₁ bx) ;
               ⟨ cc , bx ⟩ → inj₂ (inj₂ bx) }
    ; from = λ { (inj₁ x) → ⟨ aa , x ⟩ ;
                 (inj₂ (inj₁ y)) → ⟨ bb , y ⟩ ;
                 (inj₂ (inj₂ z)) → ⟨ cc , z ⟩ }
    ; from∘to = λ { ⟨ aa , snd ⟩ → refl ;
                    ⟨ bb , snd ⟩ → refl ;
                    ⟨ cc , snd ⟩ → refl  }
    ; to∘from = λ { (inj₁ x) → refl ;
                    (inj₂ (inj₁ y)) → refl ;
                    (inj₂ (inj₂ z)) → refl }
    }

```

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

```
-- Your code goes here
```

#### Exercise `∃-|-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

```
-- Your code goes here
```


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:

```
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , nb ⟩ = λ z → nb (z x)
```

Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin]({{ site.baseurl }}/Naturals/#Bin),
[Bin-laws]({{ site.baseurl }}/Induction/#Bin-laws), and
[Bin-predicates]({{ site.baseurl }}/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ](Can b)`.

```
-- Your code goes here
```

## Decidable


#### Exercise `_<?_` (recommended)

Analogous to the function above, define a function to decide strict inequality:

```
¬n<z : ∀ {n : ℕ} → ¬ (n < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m <? zero = no ¬n<z
zero <? suc n = yes z<s
suc m <? suc n with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)
```

#### Exercise `_≡ℕ?_` (practice)

Define a function to decide whether two naturals are equal:

```
¬z≡s : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡s ()

¬s≡z : ∀ {n : ℕ} → ¬ (suc n ≡ zero)
¬s≡z ()

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no ¬z≡s
suc m ≡ℕ? zero = no ¬s≡z
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes m≡n = yes (cong suc m≡n)
...                | no ¬m≡n = no (¬s≡s ¬m≡n)
```


#### Exercise `erasure` (practice)

Show that erasure relates corresponding boolean and decidable operations:
```
postulate
  ∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
  ∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
  not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
```

#### Exercise `iff-erasure` (recommended)

Give analogues of the `_⇔_` operation from
Chapter [Isomorphism]({{ site.baseurl }}/Isomorphism/#iff),
operation on booleans and decidables, and also show the corresponding erasure:

```
_iff_ : Bool → Bool → Bool
true  iff true  = true
false iff false = true
true  iff false = false
false iff true  = false

-- I know the above can be done with _s, but the syntax highlighting was being
-- annoying, so elaborating shuts it up

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes p ⇔-dec yes q = yes (record { to = λ _ → q ; from = λ _ → p })
no ¬p ⇔-dec no ¬q = yes (record { to = λ x → ⊥-elim (¬p x);
                                from = λ x → ⊥-elim (¬q x) })
yes p ⇔-dec no ¬q = no λ x → ¬q (_⇔_.to x p)
no ¬p ⇔-dec yes q = no λ z → ¬p (_⇔_.from z q)


iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes p) (yes p₁) = refl
iff-⇔ (yes p) (no ¬p) = refl
iff-⇔ (no ¬p) (yes p) = refl
iff-⇔ (no ¬p) (no ¬p₁) = refl
```
