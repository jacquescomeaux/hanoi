{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module GameState (n : ℕ) where

open import Data.Fin using (Fin)
open import Data.List using (List; allFin)

open List

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
