{-# OPTIONS --without-K --safe #-}

module AllFin where

open import Data.Nat using (ℕ; _≤_; _<_; _+_)
open import Data.Nat.Properties using (≤-preorder; +-monoʳ-≤; +-suc; n≤1+n)

open import Data.Fin using (Fin; fromℕ<; _↑ʳ_; toℕ)

open import Data.Fin.Properties using (≤-totalOrder)
open import Data.List using (List; allFin; tabulate; map; head)
open import Data.List.Properties using (tabulate-cong; map-tabulate)
open import Data.List.Relation.Unary.Linked using (Linked; _∷′_)
open import Data.List.Relation.Unary.Linked.Properties using (map⁻)
open import Data.List.Relation.Unary.Sorted.TotalOrder using (Sorted)
open import Data.Maybe using (Maybe)
open import Data.Maybe.Relation.Binary.Connected using (Connected)
open import Function using (id)

open Fin
open List
open Maybe
open Connected
open Linked
open ℕ

allℕ : (n : ℕ) → List ℕ
allℕ n = tabulate (toℕ {n})

allℕ-+-sorted : (n m : ℕ) → Linked _≤_ (tabulate (λ i → m + toℕ {n} i))
allℕ-+-sorted zero m = []
allℕ-+-sorted (suc n) m rewrite (tabulate-cong (λ x → +-suc m (toℕ {n} x))) = m≤ n ∷′ allℕ-+-sorted n (suc m)
  where
    m≤ : (n : ℕ) → Connected _≤_ (just (m + 0)) (head (tabulate (λ x → suc m + toℕ {n} x)))
    m≤ zero = just-nothing
    m≤ (suc _) = just (n≤1+n (m + 0))

allℕ-sorted : (n : ℕ) → Linked _≤_ (allℕ n)
allℕ-sorted n = allℕ-+-sorted n 0

map-toℕ-allFin-sorted : (n : ℕ) → Linked _≤_ (map (toℕ {n}) (allFin n))
map-toℕ-allFin-sorted n rewrite map-tabulate id (toℕ {n}) = allℕ-sorted n

allFin-sorted : (n : ℕ) → Sorted (≤-totalOrder n) (allFin n)
allFin-sorted n = map⁻ (map-toℕ-allFin-sorted n)
