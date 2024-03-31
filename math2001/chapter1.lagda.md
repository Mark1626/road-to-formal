```
module math2001.chapter1 where
 
open import Data.List.Base as List using (List; _∷_; [])
import Relation.Binary.PropositionalEquality as PEq
open PEq using (cong; sym; refl; _≡_)
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
  exercise₁ : (a b : ℤ)
    → a - b ≡ (+ 4)
    → a * b ≡ (+ 1)
    ---------------------------
    → (a + b) * (a + b) ≡ (+ 20)
  exercise₁ a b prop₁ prop₂ = begin
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
  exercise₂ : (r s : ℤ)
    → r + (+ 2) * s ≡ -[1+ 0 ]
    → s ≡ (+ 3)
    ---------------------
    → r ≡ -[1+ 6 ]
  exercise₂ r s prop₁ prop₂ = begin
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

  brahmagupta-id : ∀ (a b c d n : ℤ) → (a * a + n * b * b) * (c * c + n * d * d) ≡
    (a * c - n * b * d) * (a * c - n * b * d) + n * (a * d + b * c) * (a * d + b * c)
  brahmagupta-id = solve-∀

  brahmagupta-id₂ : ∀ (a b c d n : ℤ)
    → (- n * b * d + a * c) * (- n * b * d + a * c) ≡
    (a * a + n * b * b) * (c * c + n * d * d) - n * (a * d + b * c) * (a * d + b * c)
  brahmagupta-id₂ = solve-∀

  exercise₃ : (a b m n : ℤ)
    → b * b ≡ (+ 2) * a * a
    → a * m + b * n ≡ (+ 1)
    --------------------
    → ((+ 2) * a * n + b * m) * ((+ 2) * a * n + b * m) ≡ (+ 2)
  exercise₃ a b m n prop₁ prop₂ = {!begin
    2an+bm * 2an+bm ≡⟨ brahmagupta-id₂ b a m n (2-) ⟩
    (b * b + (2-) * a * a) - (2-) * am+bn * am+bn ≡⟨ cong (λ v → (b * b + (2-) * a * a) - (2-) * v * v) prop₁ ⟩
    (b * b + (2-) * a * a) - (2-) * (+ 1) * (+ 1)!}
    where
      2an+bm = ((+ 2) * a * n + b * m)
      am+bn  = (a * m + b * n)
      2- = -[1+ 1 ]
      -- This is just brahmagupta-id rearranged and n ≡ (- 2)
```
