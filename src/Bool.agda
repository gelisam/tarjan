{-# OPTIONS --no-termination --type-in-type #-}
module Bool where

open import Data.Unit
  using (⊤; tt)
open import Data.Bool public
  using (Bool; true; false; if_then_else_; not)

open import IxIO
open import Monad
open import SimpleIO


when : Bool → IO ⊤ → IO ⊤
when true  body = body
when false _    = return tt

ixWhen : {A : Set} {i j : A}
       → Bool → IxIO i i ⊤ → IxIO i i ⊤
ixWhen true  body = body
ixWhen false _    = return tt
