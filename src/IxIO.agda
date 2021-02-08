{-# OPTIONS --no-termination --type-in-type #-}
module IxIO where

open import Data.Unit
  using (⊤; tt)

open import Graph
open import Int
open import MonadClasses
open import SimpleIO


module _ {I : Set} where
  data IxIO (@erased p q : I → Set) (A : Set) : Set where
    UnsafeIxIO : IO A → IxIO p q A

  runIxIO : ∀ {@erased p q} {A} → IxIO p q A → IO A
  runIxIO (UnsafeIxIO ioA) = ioA

  lift : ∀ {@erased p} {A}
       → IO A → IxIO p p A
  lift ioA = UnsafeIxIO ioA

  IxIO-return : ∀ {@erased p} {A}
              → A → IxIO p p A
  IxIO-return a = lift do
    return a
    where
      open Monad IO-Monad

  IxIO->>= : ∀ {@erased p q r} {A B}
           → IxIO p q A
           → (A → IxIO q r B)
           → IxIO p r B
  IxIO->>= (UnsafeIxIO ioA) f = UnsafeIxIO do
    a ← ioA
    runIxIO (f a)
    where
      open Monad IO-Monad

  instance
    IxIO-Monad : IxMonad IxIO
    IxIO-Monad = record
      { return = IxIO-return
      ; _>>=_  = IxIO->>=
      }
