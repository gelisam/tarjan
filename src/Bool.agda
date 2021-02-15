{-# OPTIONS --no-termination --type-in-type #-}
module Bool where

open import Data.Bool public
  using (Bool; true; false; if_then_else_; not)
open import Data.Product
  using (_×_; _,_)
open import Data.Unit
  using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import IxIO
open import MonadClasses
open import SimpleIO


when : Bool → IO ⊤ → IO ⊤
when true  body = body
when false _    = return tt
    where
      open Monad IO-Monad

module _ {I : Set} where
  ixWhen : {@erased P : I → Set}
         → (b : Bool)
         → IxIO (λ i → b ≡ true × P i) ⊤ (λ _ → P)
         → IxIO P ⊤ (λ _ → P)
  ixWhen true body = do
    rearrange (λ _ p → refl , p)
    body
    where
      open IxMonad IxIO-Monad
  ixWhen false _ = do
    return tt
    where
      open IxMonad IxIO-Monad

  infix  0 ixIf_then_else_
  ixIf_then_else_ : {@erased P : I → Set} {A : Set} {@erased Q : A → I → Set}
                  → (b : Bool)
                  → IxIO (λ i → b ≡ true  × P i) A Q
                  → IxIO (λ i → b ≡ false × P i) A Q
                  → IxIO P A Q
  ixIf true then body else _ = do
    rearrange (λ _ p → refl , p)
    body
    where
      open IxMonad IxIO-Monad
  ixIf false then _ else body = do
    rearrange (λ _ p → refl , p)
    body
    where
      open IxMonad IxIO-Monad
