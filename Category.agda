{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Category (n : ℕ) where

open import GameState n using (GameState)
open import Move n using (Move; Path)

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Function using (flip)
open import Level using (0ℓ)

open Path

append : {A B C : GameState} → Path A B → Path B C → Path A C
append empty q = q
append (m ⨟ p) q = m ⨟ append p q

append-assoc : {A B C D : GameState} (p : Path A B) (q : Path B C) (r : Path C D) → append (append p q) r ≡ append p (append q r)
append-assoc empty q r = ≡.refl
append-assoc (m ⨟ p) q r = ≡.cong (m ⨟_) (append-assoc p q r)

append-identityʳ : {A B : GameState} (p : Path A B) → append p empty ≡ p
append-identityʳ empty = ≡.refl
append-identityʳ (m ⨟ p) = ≡.cong (m ⨟_) (append-identityʳ p)

append-identityˡ : {A B : GameState} (q : Path A B) → append empty q ≡ q
append-identityˡ _ = ≡.refl

Hanoi : Category 0ℓ 0ℓ 0ℓ
Hanoi = categoryHelper record
    { Obj = GameState
    ; _⇒_ = Path
    ; _≈_ = _≡_
    ; id = empty
    ; _∘_ = flip append
    ; assoc = λ {f = f} {g} {h} → ≡.sym (append-assoc f g h)
    ; identityˡ = λ {f = f} → append-identityʳ f
    ; identityʳ = λ {f = f} → append-identityˡ f
    ; equiv = ≡.isEquivalence
    ; ∘-resp-≈ = ≡.cong₂ (flip append)
    }
