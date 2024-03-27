```
module math2001.chapter1 where
 
open import Data.List.Base as List using (List; _∷_; [])
import Relation.Binary.PropositionalEquality as PEq
open PEq
open PEq.≡-Reasoning
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)

```

## Proving equalities

The book was doing it for ℚ, these proofs are for ℤ

```

-- Let a and b be rational numbers and suppose that 
-- a - b = 4 and ab = 1. Show that (a + b)² = 20

module chapter1 where
  open import Tactic.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)

  open import Data.Integer
  open import Data.Integer.Properties
  open import Data.Integer.Tactic.RingSolver


  -- Exercise 1.1.1
  lemma₁ : (a b : ℤ)
    → a - b ≡ (+ 4)
    → a * b ≡ (+ 1)
    ---------------------------
    → (a + b) * (a + b) ≡ (+ 20)
  lemma₁ a b prop₁ prop₂ = begin
    (a + b) * (a + b)              ≡⟨ solve (a ∷ b ∷ []) ⟩
    (a - b) * (a - b) + a * b * +4 ≡⟨ cong (λ v → v * v + 4ab) prop₁ ⟩
    +4 * +4 + 4ab                  ≡⟨ cong (λ v → +4 * +4 + v * +4) prop₂ ⟩
    +4 * +4 + +4 * +1              ≡⟨⟩
    + 20 ∎
    where
      4ab  = (a * b * (+ 4))
      +4  = + 4
      +1  = + 1

  -- Exercise 1.1.2
  lemma₂ : (r s : ℤ)
    → r + (+ 2) * s ≡ -[1+ 0 ]
    → s ≡ (+ 3)
    ---------------------
    → r ≡ -[1+ 6 ]
  lemma₂ r s prop₁ prop₂ = begin
    r                      ≡⟨ subproof r s ⟩
    r + 2s - 2s            ≡⟨ cong (λ v → v - 2s) prop₁ ⟩
    -[1+ 0 ] - 2s          ≡⟨ cong (λ v → -[1+ 0 ] - (+ 2) * v) prop₂ ⟩
    -[1+ 0 ] - (+ 2 * + 3) ≡⟨⟩
    -[1+ 0 ] - (+ 6) ∎
    where
      2s = ((+ 2) * s)
      subproof : ∀ (r s : ℤ)
        → r ≡ r + (+ 2) * s - (+ 2) * s
      subproof = solve-∀

  -- Exercise 1.1.3

  lemma₄ : ∀ (b : ℤ) → b ^ 2 ≡ b * b
  lemma₄ b rewrite (*-identityʳ b) = refl

--  brahmagupta-id : ∀ (a b n m : ℤ)
--    → ((+ 2) * a * n + b * m) ^ 2 ≡ (+ 2) * (a * m + b * n) ^ 2 + (b ^ 2 + (- 2) * a ^ 2)
--  brahmagupta-id = ?

  --lemma₃ : (a b m n : ℤ)
  --  → b * b ≡ (+ 2) * a * a
  --  → a * m + b * n ≡ (+ 1)
    --------------------
  --  → ((+ 2) * a * m + b * m) ^ 2 ≡ (+ 2)
  -- lemma₃ = {!!}


--1·1·1 : ∀ (a b : ℕ) → (a ∸ b) ≡ 4
--  → a * b ≡ 1   → (a + b) * (a + b) ≡ 20
--1·1·1 a b x x₁ = 
```
