{-# OPTIONS --no-termination --type-in-type #-}
module SimpleIO where

open import IO.Primitive public
  using (IO)
import IO.Primitive
  as IO

open import MonadClasses


instance
  IO-Monad : Monad IO
  IO-Monad = record
    { return = IO.return
    ; _>>=_  = IO._>>=_
    }
