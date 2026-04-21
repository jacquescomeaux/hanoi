{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Move (n : ℕ) where

open import Data.Fin using (Fin; #_)

open import Data.Fin.Properties using (≤-totalOrder)
open import Data.List using (List; allFin; head)
open import Data.List.Relation.Unary.Linked using (Linked; tail; _∷′_)
open import Data.Maybe using (Maybe)
open import Data.Maybe.Relation.Binary.Connected using (Connected)
open import Data.Product using (_×_; _,_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; TotalOrder)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Unary using (Pred)

open TotalOrder (≤-totalOrder n)

open ℕ
open Fin
open List
open Maybe
open Linked

open import GameState n using (Disk; TowerState; GameState; IsValidGameState; valid; state; start; end₁; end₂)

-- A valid move
data Move : Rel GameState 0ℓ where
  t₁-t₂
      : {t₁ t₂ t₃ : TowerState}
        {d : Disk}
      → Connected _≤_ (just d) (head t₂)
      → Move
        (state (d ∷ t₁) t₂ t₃)
        (state t₁ (d ∷ t₂) t₃)
  t₁-t₃
      : {t₁ t₂ t₃ : TowerState}
        {d : Disk}
      → Connected _≤_ (just d) (head t₃)
      → Move
        (state (d ∷ t₁) t₂ t₃)
        (state t₁ t₂ (d ∷ t₃))
  t₂-t₃
      : {t₁ t₂ t₃ : TowerState}
        {d : Disk}
      → Connected _≤_ (just d) (head t₃)
      → Move
        (state t₁ (d ∷ t₂) t₃)
        (state t₁ t₂ (d ∷ t₃))
  t₂-t₁
      : {t₁ t₂ t₃ : TowerState}
        {d : Disk}
      → Connected _≤_ (just d) (head t₁)
      → Move
        (state t₁ (d ∷ t₂) t₃)
        (state (d ∷ t₁) t₂ t₃)
  t₃-t₁
      : {t₁ t₂ t₃ : TowerState}
        {d : Disk}
      → Connected _≤_ (just d) (head t₁)
      → Move
        (state t₁ t₂ (d ∷ t₃))
        (state (d ∷ t₁) t₂ t₃)
  t₃-t₂
      : {t₁ t₂ t₃ : TowerState}
        {d : Disk}
      → Connected _≤_ (just d) (head t₂)
      → Move
        (state t₁ t₂ (d ∷ t₃))
        (state t₁ (d ∷ t₂) t₃)

-- Sequences of valid moves
data Path : Rel GameState 0ℓ where
  empty : {σ : GameState} → Path σ σ
  _⨟_
      : {σ σ′ τ : GameState}
      → Move σ σ′
      → Path σ′ τ
      → Path σ τ

infixr 4 _⨟_

Solution₁ Solution₂ : Set
Solution₁ = Path start end₁
Solution₂ = Path start end₂

-- A valid move preserves valid games states
move-resp-valid : {σ τ : GameState} → Move σ τ → IsValidGameState σ → IsValidGameState τ
move-resp-valid (t₁-t₂ d≤t₂) (valid t₁ t₂ t₃) = valid (tail t₁) (d≤t₂ ∷′ t₂) t₃
move-resp-valid (t₁-t₃ d≤t₃) (valid t₁ t₂ t₃) = valid (tail t₁) t₂ (d≤t₃ ∷′ t₃)
move-resp-valid (t₂-t₃ d≤t₃) (valid t₁ t₂ t₃) = valid t₁ (tail t₂) (d≤t₃ ∷′ t₃)
move-resp-valid (t₂-t₁ d≤t₁) (valid t₁ t₂ t₃) = valid (d≤t₁ ∷′ t₁) (tail t₂) t₃
move-resp-valid (t₃-t₁ d≤t₁) (valid t₁ t₂ t₃) = valid (d≤t₁ ∷′ t₁) t₂ (tail t₃)
move-resp-valid (t₃-t₂ d≤t₂) (valid t₁ t₂ t₃) = valid t₁ (d≤t₂ ∷′ t₂) (tail t₃)
