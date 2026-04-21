{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module GameState (n : ℕ) where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using (≤-totalOrder)
open import AllFin using (allFin-sorted)
open import Data.List using (List; allFin)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Relation.Unary.Sorted.TotalOrder (≤-totalOrder n) using (Sorted)

open List
open Linked

-- n disk types
Disk : Set
Disk = Fin n

-- A tower state is list of
TowerState : Set
TowerState = List Disk

-- A game state consists of three tower states
record GameState : Set where
  constructor state
  field
    t₁ t₂ t₃ : TowerState

-- The start state
start : GameState
start = state (allFin n) [] []

-- The end states
end₁ : GameState
end₁ = state [] (allFin n) []

end₂ : GameState
end₂ = state [] [] (allFin n)

-- A game state is valid when all three towers are sorted
record IsValidGameState (σ : GameState) : Set where
  constructor valid
  open GameState σ
  field
    t₁-valid : Sorted t₁
    t₂-valid : Sorted t₂
    t₃-valid : Sorted t₃

record ValidGameState : Set where
  field
    σ : GameState
    σ-valid : IsValidGameState σ

-- The start state is valid
start-valid : IsValidGameState start
start-valid = valid (allFin-sorted n) [] []

-- The end states are valid
end₁-valid : IsValidGameState end₁
end₁-valid = valid [] (allFin-sorted n) []

end₂-valid : IsValidGameState end₂
end₂-valid = valid [] [] (allFin-sorted n)
