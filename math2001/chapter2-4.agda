module math2001.chapter2-4 where

import Relation.Binary.PropositionalEquality as Peq
open Peq using (cong; cong₂; refl; sym; _≡_; _≢_)
open Peq.≡-Reasoning

open import Data.List.Base as List using (List; _∷_; [])

open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

module and-exercise where
  open import Data.Integer
  open import Tactic.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)
  open import Data.Integer.Properties
  open import Data.Integer.Tactic.RingSolver

  exercise₁ : {x y : ℤ}
    → ((+ 2) * x - y ≡ (+ 4)) × (y - x + (+ 1) ≡ (+ 2))
    -------------------
    → x ≡ (+ 5)
  exercise₁ {x} {y} (prop₁ , prop₂) = begin
    x                                         ≡⟨ solve (x ∷ y ∷ []) ⟩
    ((+ 2) * x - y) + (y - x + (+ 1)) - (+ 1) ≡⟨ cong₂ (λ v₁ v₂ → v₁ + v₂ - (+ 1)) prop₁ prop₂ ⟩
    (+ 4) + (+ 2) - (+ 1)                     ≡⟨⟩
    (+ 5)                                     ∎

