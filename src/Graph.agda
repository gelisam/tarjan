{-# OPTIONS --no-termination --type-in-type #-}
module Graph where

open import Data.List public
  using (List; []; _∷_; _++_)

open import Array
open import Int
open import Monad
open import SimpleIO


Node : Set
Node = Int

-- entry n lists that node's outgoing edges
Graph : Set
Graph = Array (List Node)

-- the example graph uses 1-based indexing, convert those to 0-based
private
  node : ℕ → Node
  node n = pred (fromℕ n)

-- the graph at https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
mkExampleGraph : IO Graph
mkExampleGraph = do
  g ← newArray (fromℕ 8) []
  g [ node 1 ]≔ (node 2 ∷ [])
  g [ node 2 ]≔ (node 3 ∷ [])
  g [ node 3 ]≔ (node 1 ∷ [])
  g [ node 4 ]≔ (node 2 ∷ node 3 ∷ node 5 ∷ [])
  g [ node 5 ]≔ (node 4 ∷ node 6 ∷ [])
  g [ node 6 ]≔ (node 3 ∷ node 7 ∷ [])
  g [ node 7 ]≔ (node 6 ∷ [])
  g [ node 8 ]≔ (node 5 ∷ node 7 ∷ node 8 ∷ [])
  return g
