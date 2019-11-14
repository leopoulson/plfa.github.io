module Iff where

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
