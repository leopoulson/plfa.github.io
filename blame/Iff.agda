module Iff where

infix 20 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
