---
title     : "Assignment1: TSPL Assignment 1"
layout    : page
permalink : /TSPL/2019/Assignment1/
---

```
module Assignment1 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

<!-- Submit your homework using the "submit" command. -->
Please ensure your files execute correctly under Agda!

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import plfa.part1.Relations using (_<_; z<s; s<s; zero; suc; even; odd)
```

## Naturals

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))
```

#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.

```
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩ --inductive case
    suc (2 + 4)
  ≡⟨⟩ --ind. case
    suc (suc (1 + 4))
  ≡⟨⟩ --ind. case
    suc (suc (suc (0 + 4)))
  ≡⟨⟩ --base case!
    suc (suc (suc (4)))
  ≡⟨⟩ --reducing
    7
  ∎
```

#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.

```
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎
```

#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.

```
_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (suc m) = n * (n ^ m)
```

```
_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
  ∎
```

#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```
_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎
```

```
_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎
```

#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
```
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
```
For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

```
inc : Bin → Bin
inc nil = x1 nil
inc (x0 m) = x1 m
inc (x1 m) = x0 (inc m)
```

```
_ : inc (inc (inc (inc nil))) ≡ x0 x0 x1 nil
_ =
  begin
    inc (inc (inc (inc nil)))
  ≡⟨⟩
    inc (inc (inc (x1 nil)))
  ≡⟨⟩
    inc (inc (x0 x1 nil))
  ≡⟨⟩
    inc (x1 x1 nil)
  ≡⟨⟩
    x0 x0 x1 nil
  ∎
```

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

```
to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * (from n)
from (x1 n) = 1 + 2 * (from n)
```

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

```
_ : to 4 ≡ x0 x0 x1 nil
_ =
  begin
    to 4
  ≡⟨⟩
    inc (to 3)
  ≡⟨⟩
    inc (inc (to 2))
  ≡⟨⟩
    inc (inc (inc (to 1)))
  ≡⟨⟩
    inc (inc (inc (inc (to 0))))
  ≡⟨⟩
    inc (inc (inc (inc (nil))))
  ≡⟨⟩
    x0 x0 x1 nil
  ∎

_ : from (x0 x0 x1 nil) ≡ 4
_ =
  begin
    from (x0 x0 x1 nil)
  ≡⟨⟩
    2 * (from (x0 x1 nil))
  ≡⟨⟩
    2 * (2 * (from (x1 nil)))
  ≡⟨⟩
    2 * (2 * (1 + 2 * (from nil)))
  ≡⟨⟩
    2 * (2 * (1 + 2 * 0))
  ≡⟨⟩
    4
  ∎
```

## Induction

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

```
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎
```

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

```
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩ --defn of +
    (suc (m + n)) * p
  ≡⟨⟩ --defn of *
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+ m n p)⟩
    p + ((m * p) + (n * p))
  ≡⟨ sym (+-assoc p (m * p) (n * p))⟩
    (p + (m * p)) + n * p
  ≡⟨⟩ --defn of *
    (suc m * p) + n * p
  ∎
```

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

```
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
  -- begin
  --   (zero * n) * p
  -- ≡⟨⟩
  --   zero * p
  -- ≡⟨⟩
  --   zero
  -- ≡⟨⟩
  --   zero * (n * p)
  -- ∎
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + ((m * n) * p)
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + (m * (n * p))
  ≡⟨⟩
    (suc m) * (n * p)
  ∎
```

#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

```
*-cancelʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-cancelʳ zero = refl
*-cancelʳ (suc m) =
  begin
    (suc m) * zero
  ≡⟨⟩
    zero + (m * zero)
  ≡⟨ cong (zero +_) (*-cancelʳ m) ⟩
    zero + zero
  ≡⟨⟩
    zero
  ∎

suc-move : ∀ (m n : ℕ) → suc m + n ≡ m + suc n
suc-move m n =
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ≡⟨ +-comm (suc n) m ⟩
    m + suc n
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-cancelʳ n)⟩
    n * zero
  ∎
*-comm m zero =
  begin
    m * zero
  ≡⟨ *-cancelʳ m ⟩
    zero
  ≡⟨⟩
    zero * m
  ∎
*-comm (suc m) (suc n) =
  begin
    suc m * suc n
  ≡⟨⟩
    suc n + (m * suc n)
  ≡⟨ cong ((suc n) +_) (*-comm m (suc n))⟩
    suc n + (suc n * m)
  ≡⟨⟩
    suc n + (m + (n * m))
  ≡⟨ sym (+-assoc (suc n) m (n * m)) ⟩
    suc n + m + (n * m)
  ≡⟨ cong (_+ (n * m)) (suc-move n m) ⟩
    n + suc m + (n * m)
  ≡⟨ cong (_+ (n * m)) (+-comm n (suc m)) ⟩
    suc m + n + (n * m)
  ≡⟨ cong ((suc m + n) +_) (*-comm n m)⟩
    suc m + n + (m * n)
  ≡⟨ +-assoc (suc m) n (m * n) ⟩
    suc m + (n + (m * n))
  ≡⟨⟩
    suc m + suc m * n
  ≡⟨ cong ((suc m) +_) (*-comm (suc m) n) ⟩
    suc m + n * suc m
  ≡⟨⟩
    suc n * suc m
  ∎
```


#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

```
∸-identityˡ : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-identityˡ zero =
  begin
    zero ∸ zero
  ≡⟨⟩
    zero
  ∎
∸-identityˡ (suc n) =
  begin
    zero ∸ (suc n)
  ≡⟨⟩
    zero
  ∎
```

#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.

```
-- inc-id : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
-- inc-id nil =
--   begin
--     from (inc nil)
--   ≡⟨⟩
--     from (x1 nil)
--   ≡⟨⟩
--     1
--   ≡⟨⟩
--     suc zero
--   ≡⟨⟩
--     suc (from nil)
--   ∎
-- inc-id (x0 n) =
--   begin
--     from (inc (x0 n))
--   ≡⟨⟩
--     from (x1 n)
--   ≡⟨⟩
--     1 + 2 * (from n)
--   ≡⟨⟩
--     suc (2 * (from n))
--   ≡⟨⟩
--     suc (from (x0 n))
--   ∎
-- inc-id (x1 n) =
--   begin
--     from (inc (x1 n))
--   ≡⟨⟩
--     from (x0 (inc n))
--   ≡⟨⟩
--     2 * (from (inc n))
--   ≡⟨ cong (2 *_) (inc-id n)⟩
--     2 * (suc (from n))
--   ≡⟨⟩
--     suc (suc (2 * (from n)))
--   ≡⟨⟩
--     suc (1 + (2 * (from n)))
--   ≡⟨⟩
--     suc (from (x1 n))
--   ∎
```

## Relations


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

```
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p

-- remember that the case
-- <-trans z<s z<s
-- is impossible, so we don't need to worry about it
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

```
≤-iff-<ˡ : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-iff-<ˡ zero    n (s≤s z≤p) = z<s

-- remmeber again to split cases more carefully
≤-iff-<ˡ (suc m) (suc n) (s≤s m≤n) = s<s (≤-iff-<ˡ m n m≤n)

≤-iff-<ʳ : ∀ (m n : ℕ) → m < n → suc m ≤ n
≤-iff-<ʳ zero n z<s = s≤s z≤n
≤-iff-<ʳ (suc m) (suc n) (s<s m<n) = s≤s (≤-iff-<ʳ m n m<n)
```

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

```
o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    -----
  → even (m + n)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----
  → odd (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)

e+o≡o zero on = on
e+o≡o (suc om) on = suc (o+o≡e om on)

```

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)
