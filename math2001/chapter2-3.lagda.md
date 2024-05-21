```agda

module math2001.chapter2-3 where

import Relation.Binary.PropositionalEquality as Peq
open Peq using (cong; cong₂; refl; sym; _≡_; _≢_)
open Peq.≡-Reasoning

open import Data.Product
-- using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

-- open import Data.Integer

module int-examples where
  open import Data.Integer
  open import Data.Integer.Properties

  

  -- 2.3.1
  example₁ : (x y : ℤ) → x ≡ (+ 1) ⊎ y ≡ -1ℤ → x * y + x ≡ y + (+ 1)
  example₁ x y (inj₁ x≡1) = begin
    x * y + x         ≡⟨ cong (λ v → v * y + v) x≡1 ⟩
    (+ 1) * y + (+ 1) ≡⟨ cong (_+ (+ 1)) (*-identityˡ y) ⟩
    y + (+ 1)         ∎
  example₁ x y (inj₂ y≡-1) = begin
    x * y + x          ≡⟨ cong (λ v → v + x) (*-comm x y) ⟩
    y * x + x          ≡⟨ cong (λ v → v * x + x) y≡-1 ⟩
    -1ℤ * x + x        ≡⟨ cong (λ v → v + x) (-1*i≡-i x) ⟩
    - x + x            ≡⟨ +-inverseˡ x ⟩
    0ℤ                 ≡⟨⟩
    -[1+ 0 ] + (+ 1)   ≡⟨ cong (λ v → v + (+ 1)) (sym y≡-1) ⟩
    y + (+ 1)          ∎


module nat-examples where
  open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_; s≤s; z≤n; _∸_; _/_)
  open import Data.Nat.Properties
  open import Tactic.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)
  open import Data.Nat.Tactic.RingSolver
  open import Data.Nat.DivMod

  -- 2.3.2
  -- A simple pattern match proof
  -- The mechanics of proof uses different route with n ≤ 1 ⊎ 2 ≤ n
  exercise₁ : (n : ℕ) → n * n ≢ 2
  exercise₁ zero = λ ()
  exercise₁ (suc zero) = λ ()
  exercise₁ (suc (suc zero)) = λ ()
  exercise₁ (suc (suc (suc n))) = λ ()

  -- 2.3.3
  exercise₂ : {x : ℕ} → 2 * x + 1 ≡ 5 → x ≡ 1 ⊎ x ≡ 2
  exercise₂ {x} prop₁ = inj₂ (begin
    x                     ≡⟨ sym (m*n/n≡m x 2) ⟩
    x * 2 / 2             ≡⟨ cong (λ v → v / 2) (*-comm x 2) ⟩
    2 * x / 2             ≡⟨ cong (λ v → v / 2) (sym (m+n∸n≡m (2 * x) 1)) ⟩
    (2 * x + 1 ∸ 1) / 2   ≡⟨ cong (λ v → (v ∸ 1) / 2) prop₁ ⟩
    (5 ∸ 1) / 2           ≡⟨⟩
    2                     ∎)

--  open import Data.Nat.Divisibility



```
