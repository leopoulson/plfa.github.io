---
title     : "Assignment3: TSPL Assignment 3"
layout    : page
permalink : /TSPL/2019/Assignment3/
---

```
module Assignment3 where
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
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Algebra.Structures using (IsMonoid)
open import Level using (Level)
open import Relation.Unary using (Decidable)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning
open import plfa.part1.Lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_];
  _++_; reverse; map; foldr; sum; All; Any; here; there; _∈_;
  ++-identityʳ; ++-assoc)
open import plfa.part2.Lambda hiding (ƛ′_⇒_; case′_[zero⇒_|suc_⇒_]; μ′_⇒_; plus′; begin_; _∎)
open import plfa.part2.Properties hiding (value?; unstuck; preserves; wttdgs)
```


## Lists

#### Exercise `reverse-++-distrib` (recommended)

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

```
reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse (( x ∷ xs ) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎
```

#### Exercise `reverse-involutive` (recommended)

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs

```
reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    [ x ] ++ reverse (reverse xs)
  ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
    [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎
```


#### Exercise `map-compose` (practice)

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) ≡ map g ∘ map f

The last step of the proof requires extensionality.

#### Exercise `map-++-distribute` (practice)

Prove the following relationship between map and append:

   map f (xs ++ ys) ≡ map f xs ++ map f ys

#### Exercise `map-Tree` (practice)

Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
```
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
```
Define a suitable map operator over trees:
```
postulate
  map-Tree : ∀ {A B C D : Set}
    → (A → C) → (B → D) → Tree A B → Tree C D
```


#### Exercise `product` (recommended)

Use fold to define a function to find the product of a list of numbers.
For example:

    product [ 1 , 2 , 3 , 4 ] ≡ 24

```
product : List ℕ → ℕ
product = foldr _*_ 1
```

#### Exercise `foldr-++` (recommended)

Show that fold and append are related as follows:
```
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys)⟩
    x ⊗ (foldr _⊗_ (foldr _⊗_ e ys) xs)
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
  ∎
```


#### Exercise `map-is-foldr` (practice)

Show that map can be defined using fold:
```
postulate
  map-is-foldr : ∀ {A B : Set} {f : A → B} →
    map f ≡ foldr (λ x xs → f x ∷ xs) []
```
This requires extensionality.

#### Exercise `fold-Tree` (practice)

Define a suitable fold function for the type of trees given earlier:
```
postulate
  fold-Tree : ∀ {A B C : Set}
    → (A → C) → (C → B → C → C) → Tree A B → C
```

```
-- Your code goes here
```

#### Exercise `map-is-fold-Tree` (practice)

Demonstrate an analogue of `map-is-foldr` for the type of trees.

```
-- Your code goes here
```

#### Exercise `sum-downFrom` (stretch)

Define a function that counts down as follows:
```
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
```
For example:
```
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:
```
postulate
  sum-downFrom : ∀ (n : ℕ)
    → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
```


#### Exercise `foldl` (practice)

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

```
-- Your code goes here
```


#### Exercise `foldr-monoid-foldl` (practice)

Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

```
-- Your code goes here
```


#### Exercise `Any-++-⇔` (recommended)

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.

```
xs-→-xsys : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → Any P xs → Any P (xs ++ ys)
xs-→-xsys (x ∷ xs) ys (here x') = here x'
xs-→-xsys (x ∷ xs) ys (there Pxs) = there (xs-→-xsys xs ys Pxs)

ys-→-xsys : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → Any P ys → Any P (xs ++ ys)
ys-→-xsys [] ys any = any
ys-→-xsys (x ∷ xs) ys any = there (ys-→-xsys xs ys any)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
    → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to [] ys Pys = inj₂ Pys
  to (x ∷ xs) ys (here x₁) = inj₁ (here x₁)
  to (x ∷ xs) ys (there Pxsys) with to xs ys Pxsys
  ...                             | inj₁ Pxs = inj₁ (there Pxs)
  ...                             | inj₂ Pys = inj₂ Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
    → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
  from xs ys (inj₁ Pxs) = xs-→-xsys xs ys Pxs
  from xs ys (inj₂ Pys) = ys-→-xsys xs ys Pys
```

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

```
-- Your code goes here
```


#### Exercise `¬Any≃All¬` (recommended)

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs

```
to-lem : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
to-lem [] any = []
to-lem (x ∷ xs) any = (λ Px → any (here Px)) ∷ to-lem xs (λ z → any (there z))

from-lem : ∀ {A : Set} {P : A → Set} (xs : List A)
  → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
from-lem .[] [] ()
from-lem .(_ ∷ _) (Px ∷ all) (here x) = Px x
from-lem .(_ ∷ _) (Px ∷ all) (there any) = from-lem _ all any

from∘to-lem : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (any : (¬_ ∘ Any P) xs) → from-lem xs (to-lem xs any) ≡ any
from∘to-lem [] any = extensionality λ ()
from∘to-lem (x ∷ xs) any = extensionality λ { any' → ⊥-elim (any any') }

to∘from-lem : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (all : All ((λ {x} → ¬_) ∘ P) xs) → to-lem xs (from-lem xs all) ≡ all
to∘from-lem [] [] = refl
to∘from-lem (x ∷ xs) (Px ∷ Pxs) = cong (Px ∷_) (to∘from-lem xs Pxs)

¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs =
  record
    { to = λ any → to-lem xs any
    ; from = λ all → from-lem xs all
    ; from∘to = λ any → from∘to-lem xs any
    ; to∘from = λ all → to∘from-lem xs all
    }
```

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism]({{ site.baseurl }}/Equality/#unipoly)?)

Do we also have the following?

    (¬_ ∘ All P) xs ≃ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.

This doesn't hold. We know that not everything in xs satisfies the property P;
however, from this we can not say /which one/ - we just have a proof that it
doesn't hold for each one. As such we have no way to construct Any (¬_ ∘ P) xs.


#### Exercise `All-∀` (practice)

Show that `All P xs` is isomorphic to `∀ {x} → x ∈ xs → P x`.



#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```
-- You code goes here
```


#### Exercise `any?` (stretch)

Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.

```
-- Your code goes here
```


#### Exercise `filter?` (stretch)

Define the following variant of the traditional `filter` function on lists,
which given a decidable predicate and a list returns all elements of the
list satisfying the predicate:
```
postulate
  filter? : ∀ {A : Set} {P : A → Set}
    → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
```



## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

```
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n" ) ]
```


#### Exercise `mulᶜ` (practice)

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

```
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
       ` "m" · (plusᶜ · ` "n") · (` "n" · ` "s" · ` "z")
```


#### Exercise `primed` (stretch) {#primed}

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
```
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥
```
We intend to apply the function only when the first term is a variable, which we
indicate by postulating a term `impossible` of the empty type `⊥`.  If we use
C-c C-n to normalise the term

  ƛ′ two ⇒ two

Agda will return an answer warning us that the impossible has occurred:

  ⊥-elim (plfa.part2.Lambda.impossible (`` `suc (`suc `zero)) (`suc (`suc `zero)) ``)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.

The definition of `plus` can now be written as follows:
```
plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"
```
Write out the definition of multiplication in the same style.


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

```
-- Your code goes here
```


#### Exercise `—↠≲—↠′` (practice)

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

```
-- Your code goes here
```

#### Exercise `plus-example` (practice)

Write out the reduction sequence demonstrating that one plus one is two.

```
-- Your code goes here
```


#### Exercise `Context-≃` (practice)

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

```
-- Your code goes here
```

-- mul : Term
-- mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
--         case ` "m"
--           [zero⇒ ` "n"
--           |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n" ) ]
--
-- plus : Term
-- plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
--          case ` "m"
--            [zero⇒ ` "n"
--            |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

```
mul-type : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
mul-type = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m)
                       (⊢` ∋n)
                       (⊢plus · ⊢` ∋n' · (⊢` ∋* · ⊢` ∋m' · ⊢` ∋n')))))
  where
    ∋m  = (S (λ ()) Z)
    ∋n  = Z
    ∋n' = (S (λ ()) Z)
    ∋m' = Z
    ∋* = (S (λ()) (S (λ()) (S (λ ()) Z)))

```


#### Exercise `mulᶜ-type` (practice)

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

```

```



## Properties

#### Exercise `Progress-≃` (practice)

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.

```
-- Your code goes here
```

#### Exercise `progress′` (practice)

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.

```
-- Your code goes here
```

#### Exercise `value?` (practice)

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value:
```
postulate
  value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
```

#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.

```
-- Your code goes here
```


#### Exercise `mul-eval` (recommended)

Using the evaluator, confirm that two times two is four.

I moved this to the bottom of the page as it's very long and gets in the way.


#### Exercise: `progress-preservation` (practice)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

```
-- Your code goes here
```


#### Exercise `subject_expansion` (practice)

We say that `M` _reduces_ to `N` if `M —→ N`,
but we can also describe the same situation by saying
that `N` _expands_ to `M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.

```
-- Your code goes here
```


#### Exercise `stuck` (practice)

Give an example of an ill-typed term that does get stuck.

```
-- Your code goes here
```

#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.

```
unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck form ⟨ NM , ¬VM ⟩ with progress form
... | step M→N = NM M→N
... | done V = ¬VM V
```

```
preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves mt (M _—↠_.∎) = mt
preserves lt (L —→⟨ L→M ⟩ M↠N) = preserves (preserve lt L→M) M↠N
```

```
wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    --------
  → ¬ (Stuck N)
wttdgs mt M↠N = unstuck (preserves mt M↠N)
```

#### Exercise `mul-eval`

Here we are.

```
⊢2*2 : ∅ ⊢ mul · two · two ⦂ `ℕ
⊢2*2 = mul-type · ⊢two · ⊢two

```

_ : eval (gas 100) ⊢2*2 ≡
  steps
  ((μ "*" ⇒
  (ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
    (μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "n"
    · (` "*" · ` "m" · ` "n")
    ])))
 · `suc (`suc `zero)
 · `suc (`suc `zero)
 —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
 (ƛ "m" ⇒
  (ƛ "n" ⇒
   case ` "m" [zero⇒ ` "n" |suc "m" ⇒
   (μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "n"
   ·
   ((μ "*" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       (μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "n"
       · (` "*" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ]))
 · `suc (`suc `zero)
 · `suc (`suc `zero)
 —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  (μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · ` "n"
  ·
  ((μ "*" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "n"
      · (` "*" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 · `suc (`suc `zero)
 —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
 case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
 (μ "+" ⇒
  (ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
    ])))
 · `suc (`suc `zero)
 ·
 ((μ "*" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "n"
     · (` "*" · ` "m" · ` "n")
     ])))
  · ` "m"
  · `suc (`suc `zero))
 ]
 —→⟨ β-suc (V-suc V-zero) ⟩
 (μ "+" ⇒
  (ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
    ])))
 · `suc (`suc `zero)
 ·
 ((μ "*" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "n"
     · (` "*" · ` "m" · ` "n")
     ])))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
 (ƛ "m" ⇒
  (ƛ "n" ⇒
   case ` "m" [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ]))
 · `suc (`suc `zero)
 ·
 ((μ "*" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "n"
     · (` "*" · ` "m" · ` "n")
     ])))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((μ "*" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "n"
     · (` "*" · ` "m" · ` "n")
     ])))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
    (μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "n"
    ·
    ((μ "*" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        (μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "n"
        · (` "*" · ` "m" · ` "n")
        ])))
     · ` "m"
     · ` "n")
    ]))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "n" ⇒
   case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
   (μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "n"
   ·
   ((μ "*" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
       (μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
       · ` "n"
       · (` "*" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
 (μ "+" ⇒
  (ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
    ])))
 · `suc (`suc `zero)
 ·
 ((μ "*" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "n"
     · (` "*" · ` "m" · ` "n")
     ])))
  · ` "m"
  · `suc (`suc `zero))
 ]
 —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · `suc (`suc `zero)
  ·
  ((μ "*" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "n"
      · (` "*" · ` "m" · ` "n")
      ])))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · ` "n")
    ]))
  · `suc (`suc `zero)
  ·
  ((μ "*" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "n"
      · (` "*" · ` "m" · ` "n")
      ])))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "n" ⇒
   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  ·
  ((μ "*" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "n"
      · (` "*" · ` "m" · ` "n")
      ])))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "n" ⇒
   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  ·
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     (μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "n"
     ·
     ((μ "*" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒
         (μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
            ])))
         · ` "n"
         · (` "*" · ` "m" · ` "n")
         ])))
      · ` "m"
      · ` "n")
     ]))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "n" ⇒
   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  ·
  ((ƛ "n" ⇒
    case `zero [zero⇒ ` "n" |suc "m" ⇒
    (μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "n"
    ·
    ((μ "*" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒
        (μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ])))
        · ` "n"
        · (` "*" · ` "m" · ` "n")
        ])))
     · ` "m"
     · ` "n")
    ])
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "n" ⇒
   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  ·
  case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
  (μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · `suc (`suc `zero)
  ·
  ((μ "*" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      (μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "n"
      · (` "*" · ` "m" · ` "n")
      ])))
   · ` "m"
   · `suc (`suc `zero))
  ])
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 ((ƛ "n" ⇒
   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
 `suc
 ((μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · ` "m"
  · `suc (`suc `zero))
 ]
 —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 ((μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 ((ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · ` "n")
    ]))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 ((ƛ "n" ⇒
   case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
 `suc
 ((μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · ` "m"
  · `suc (`suc `zero))
 ]
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 (`suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 (`suc
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · ` "n")
     ]))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 (`suc
  ((ƛ "n" ⇒
    case `zero [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · ` "n")
    ])
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero))))) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 ·
 `suc
 (`suc
  case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · `suc (`suc `zero))
  ])
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
 (ƛ "n" ⇒
  case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · ` "n")
  ])
 · `suc (`suc (`suc (`suc `zero)))
 —→⟨ β-ƛ (V-suc (V-suc (V-suc (V-suc V-zero)))) ⟩
 case `suc (`suc `zero) [zero⇒ `suc (`suc (`suc (`suc `zero))) |suc
 "m" ⇒
 `suc
 ((μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · ` "m"
  · `suc (`suc (`suc (`suc `zero))))
 ]
 —→⟨ β-suc (V-suc V-zero) ⟩
 `suc
 ((μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · `suc `zero
  · `suc (`suc (`suc (`suc `zero))))
 —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
 `suc
 ((ƛ "m" ⇒
   (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · ` "n")
    ]))
  · `suc `zero
  · `suc (`suc (`suc (`suc `zero))))
 —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
 `suc
 ((ƛ "n" ⇒
   case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
       ])))
    · ` "m"
    · ` "n")
   ])
  · `suc (`suc (`suc (`suc `zero))))
 —→⟨ ξ-suc (β-ƛ (V-suc (V-suc (V-suc (V-suc V-zero))))) ⟩
 `suc
 case `suc `zero [zero⇒ `suc (`suc (`suc (`suc `zero))) |suc "m" ⇒
 `suc
 ((μ "+" ⇒
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
     ])))
  · ` "m"
  · `suc (`suc (`suc (`suc `zero))))
 ]
 —→⟨ ξ-suc (β-suc V-zero) ⟩
 `suc
 (`suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · `zero
   · `suc (`suc (`suc (`suc `zero)))))
 —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
 `suc
 (`suc
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
         ])))
      · ` "m"
      · ` "n")
     ]))
   · `zero
   · `suc (`suc (`suc (`suc `zero)))))
 —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
 `suc
 (`suc
  ((ƛ "n" ⇒
    case `zero [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
     · ` "m"
     · ` "n")
    ])
   · `suc (`suc (`suc (`suc `zero)))))
 —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc (V-suc (V-suc V-zero)))))) ⟩
 `suc
 (`suc
  case `zero [zero⇒ `suc (`suc (`suc (`suc `zero))) |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
   · ` "m"
   · `suc (`suc (`suc (`suc `zero))))
  ])
 —→⟨ ξ-suc (ξ-suc β-zero) ⟩
 `suc (`suc (`suc (`suc (`suc (`suc `zero))))) _—↠_.∎)
  (done (V-suc (V-suc (V-suc (V-suc (V-suc (V-suc V-zero)))))))
_ = refl

