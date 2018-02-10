module Main where

open import Data.List using (List; map; upTo)
open import Data.Vec using (Vec)

open import Bits

test : List (Vec Bit _)
test = map bits (upTo 10)
