{-# OPTIONS --no-termination --type-in-type #-}
module IORef where

open import Data.Unit
  using (⊤)

open import Int
open import SimpleIO


postulate
  IORef         : Set → Set
  newIORef      : ∀ {@erased A} → A → IO (IORef A)
  readIORef     : ∀ {@erased A} → IORef A → IO A
  writeIORef    : ∀ {@erased A} → IORef A → A → IO ⊤
  modifyIORef   : ∀ {@erased A} → IORef A → (A → A) → IO ⊤
  printIntIORef : IORef Int → IO ⊤
{-# FOREIGN GHC import Data.IORef #-}
{-# COMPILE GHC IORef       = type IORef #-}
{-# COMPILE GHC newIORef    = \_ -> newIORef #-}
{-# COMPILE GHC readIORef   = \_ -> readIORef #-}
{-# COMPILE GHC writeIORef  = \_ -> writeIORef #-}
{-# COMPILE GHC modifyIORef = \_ -> modifyIORef #-}
{-# FOREIGN GHC
  printIORef :: Show a => IORef a -> IO ()
  printIORef ref = do
    a <- readIORef ref
    print a
#-}
{-# COMPILE GHC printIntIORef = printIORef #-}
