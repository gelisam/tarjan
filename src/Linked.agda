{-# OPTIONS --no-termination --type-in-type #-}
module Linked where

open import Relation.Binary.PropositionalEquality
  using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)


module _ {A : Set} where
  record Linked (@erased expected : A) : Set where
    constructor _,_
    field
      actual : A
      @erased link : actual ≡ expected

  unsafeLinked : ∀ (@erased expected) → (actual : A) → Linked expected
  unsafeLinked expected actual = actual , trustMe
