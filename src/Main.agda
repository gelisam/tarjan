module Main where

open import Data.List using (List; map; upTo)
open import Data.Vec using (toList)
open import Function using (_∘_)

open import Bits

test : List (List Bit)
test = map (toList ∘ bits) (upTo 10)
