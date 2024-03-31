```agda

module math2001.chapter2-3 where

import Relation.Binary.PropositionalEquality as Peq
open Peq using (cong; cong₂; refl; sym; _≡_)
open Peq.≡-Reasoning

open import Data.Product
-- using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

-- open import Data.Integer

module int-examples where
  open import Data.Integer
  open import Data.Integer.Properties
  
  -- 2.3.1
  example₁ : (x y : ℤ) → x ≡ (+ 1) ⊎ y ≡ (-[1+ 0 ]) → x * y + x ≡ y + (+ 1)
  example₁ x y (inj₁ x≡1) = begin
    x * y + x         ≡⟨ cong (λ v → v * y + v) x≡1 ⟩
    (+ 1) * y + (+ 1) ≡⟨ cong (_+ (+ 1)) (*-identityˡ y) ⟩
    y + (+ 1)         ∎
  example₁ x y (inj₂ y≡-1) = {!begin
    x * y + x          ≡⟨ cong (λ v → x * v + x) y≡-1 ⟩
    x * (-[1+ 0 ]) + x ≡⟨ n⊖n≡0 x ⟩
    0ℤ                 ≡⟨⟩
    -[1+ 0 ] + (+ 1)   ≡⟨ cong (λ v → v + (+ 1)) (sym y≡-1) ⟩
    y + (+ 1) ∎!}
--  begin
--    x * y + x          ≡⟨ cong (λ v → x * v + x) y≡-1 ⟩
--    x * (-[1+ 0 ]) + x ≡⟨⟩
--    0ℤ                 ≡⟨⟩
--    -[1+ 0 ] + (+ 1)   ≡⟨ cong (λ v → v + (+ 1)) (sym y≡-1) ⟩
--    y + (+ 1) ∎


module nat-examples where
  open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_; s≤s; z≤n; _∸_)
  open import Data.Nat.Properties using
    (+-identityˡ;
    +-identityʳ)

  -- 2.3.3
  exercise₁ : {x : ℕ} → 2 * x + 1 ≡ 5 → x ≡ 1 ⊎ x ≡ 2
  exercise₁ {x} prop₁ = inj₂ {!!}
    where
      open import Data.Nat.Tactic.RingSolver

  open import Data.Nat.Divisibility



```
