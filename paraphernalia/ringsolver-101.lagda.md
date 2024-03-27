# Ring Solver

A ring solver can automatically solve propositional equivalences
containing a `_+_` and a `_*_` (A ring basically id, zero, +, *)

```
module ringsolver-101 where

open import Data.List
open import Tactic.RingSolver.Core.AlmostCommutativeRing
  using (AlmostCommutativeRing)

import Relation.Binary.PropositionalEquality as PEq
open PEq
open PEq.≡-Reasoning

```

> Note: I'm importing Nat inside a module because some of the proofs later use Data.Integer

## Elementary equations

```
module elem-eqn₁ where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Nat.Tactic.RingSolver

  lemma₁ : ∀ (a b : ℕ)
    → (a + b) * (a + b) ≡ a * a + 2 * a * b + b * b
  lemma₁ = solve-∀

  lemma₂ : ∀ (a b : ℕ)
    → (a + b) * (a + b) * (a + b) ≡ (a * a * a) + (3 * a * a * b) + (3 * a * b * b) + (b * b * b)
  lemma₂ = solve-∀

```

## Usage in manual propositional equality reasoning chain

```
module elem-eqn₂ where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Nat.Tactic.RingSolver

  fib : ℕ → ℕ
  fib zero = 0
  fib 1    = 1
  fib (suc (suc n)) = fib (suc n) + fib n

  -- This hole can't be substituted with a simple solve-∀
  lemma₃ : ∀ (m n : ℕ) → fib (m + suc n) ≡ fib (suc m) * fib (suc n) + fib m * fib n
  lemma₃ zero n = begin
    fib (suc n) ≡⟨ sym (+-identityʳ _) ⟩
    fib (suc n) + zero ≡⟨ sym (+-identityʳ _) ⟩
    fib (suc n) + zero + zero ∎
  lemma₃ (suc m) n = begin
    fib (suc (m + suc n)) ≡⟨ cong fib (sym (+-suc m (suc n)))⟩
    fib (m + suc (suc n)) ≡⟨ lemma₃ m (suc n) ⟩
    fib (suc m) * (fib (suc n) + fib n) + fib m * fib (suc n) ≡⟨⟩
    fsm * (fsn + fn) + (fm * fsn) ≡⟨ subproof₁ fm fn fsm fsn ⟩
    (fsm + fm) * fsn + fsm * fn ∎
    where
      fsm = fib (suc m)
      fsn = fib (suc n)
      fn  = fib n
      fm  = fib m
      subproof₁ : ∀ (a b c d : ℕ) → c * (d + b) + (a * d) ≡ (c + a) * d + c * b
      subproof₁ = solve-∀
```

## Some

```
module integer-scenario where
  open import Data.Integer
  open import Data.Integer.Properties
  open import Data.Integer.Tactic.RingSolver

  brahmagupta-id : ∀ (a b c d n : ℤ) → (a * a + n * b * b) * (c * c + n * d * d) ≡
    (a * c - n * b * d) * (a * c - n * b * d) + n * (a * d + b * c) * (a * d + b * c)
  brahmagupta-id = solve-∀
```

## Reading

1. https://reasonablypolymorphic.com/blog/ring-solving/index.html

