{-# OPTIONS --no-termination --type-in-type #-}
module Bool where

open import Data.Unit
  using (⊤; tt)
open import Data.Bool public
  using (Bool; true; false; if_then_else_; not)

open import IxIO
open import MonadClasses
open import SimpleIO


when : Bool → IO ⊤ → IO ⊤
when true  body = body
when false _    = return tt
    where
      open Monad IO-Monad

ixWhen : {I : Set} {i : I}
       → Bool
       → IxIO i ⊤ (λ _ → i)
       → IxIO i ⊤ (λ _ → i)
ixWhen true  body = body
ixWhen false _    = return tt
    where
      open IxMonad IxIO-Monad
