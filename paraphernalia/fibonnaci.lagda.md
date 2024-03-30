# Some formalization on Fibonnaci identities

<!--
```agda
module paraphernalia.fibonnaci where

open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤_; s≤s; z≤n; _∸_)
open import Data.Nat.Properties using (
  *-suc;
  *-comm;
  *-distribʳ-+;
  *-distribˡ-+;
  m≤n⇒m≤n+o;
  +-∸-comm;
  +-comm;
  +-suc;
  +-identityʳ;
  +-assoc)
open import Data.Nat.Tactic.RingSolver
import Relation.Binary.PropositionalEquality as Peq
open Peq using (cong; cong₂; refl; sym; _≡_)
open Peq.≡-Reasoning

open import Data.Nat.GCD
open import Data.Nat.Divisibility

open import Data.Product using (_,_; proj₁; proj₂)
open import Function

pattern 2+ n = suc (suc n)
```
-->

## Definition

```agda
fib : ℕ → ℕ
fib 0            = 0
fib 1            = 1
fib (suc (suc n)) = fib (suc n) + fib n
```

Usage of the definition

```agda
_ : fib(3) ≡ 2
_ = refl

_ : fib(10) ≡ 55
_ = refl
```

## Properties

### ∑f(n) ≡ f(2n+1) - 1

```agda
∑fib : ℕ → ℕ
∑fib zero          = fib zero
∑fib 1             = fib 1
∑fib (suc (suc n)) = (∑fib (suc n)) + (fib (suc (suc n)))

_ : (∑fib 1) ≡ 1
_ = refl

-- n   = 0 1 2 3 4 5
-- fn  = 0 1 1 2 3 5
-- ∑fn = 0 1 2 4 7 12
_ : (∑fib 5) ≡ 12
_ = refl

∀n-1≤fn+1 : ∀ (n : ℕ) → 1 ≤ fib (suc n)
∀n-1≤fn+1 zero = s≤s z≤n
∀n-1≤fn+1 (suc n) = m≤n⇒m≤n+o (fib n) (∀n-1≤fn+1 n)

theory₁ : ∀ (n : ℕ) → (∑fib n) ≡ (fib (suc (suc (n)))) ∸ 1
theory₁ zero = refl
theory₁ 1    = refl
theory₁ (suc (suc n)) rewrite theory₁ (suc n) = begin
  fn+3 ∸ 1 + fn+2 ≡⟨ sym (+-∸-comm fn+2 (∀n-1≤fn+1 n+2)) ⟩
  fn+3 + fn+2 ∸ 1 ∎
  where
    n+2 = (suc (suc n))
    fn+3 = fib (suc n+2)
    fn+2 = fib n+2

```

---

### GCD (fib(n + 1), fib(n)) ≡ 1

This two are from [Gallai's](https://github.com/gallai) [repo](https://github.com/gallais/potpourri/blob/main/agda/papers/fibonacci/Fib.agda). I'm trying to see if I can prove it in another way.

Source of the identity is from [this site](https://web.archive.org/web/20190829195105/https://www.math.hmc.edu/funfacts/ffiles/20004.5.shtml)

```
theory₂ : ∀ (n : ℕ) → GCD (fib (suc n)) (fib n) 1
theory₂ zero = GCD.is (divides-refl 1 , divides-refl zero) proj₁
theory₂ (suc n) = GCD.sym (GCD.step (theory₂ n))
```

### fib(m+n) ≡ fib(m+1) * fib(n) + fib(m) * fib(n-1)

```agda
-- TIL: Order matters
+-swap₁ : ∀ (a b c : ℕ) → a + b + c ≡ b + a + c
+-swap₁ a b c = cong (_+ c) (+-comm a b)

+-swap₂ : ∀ (a b c : ℕ) → a + b + c ≡ a + (c + b)
+-swap₂ a b c rewrite +-assoc a b c = cong (a +_) (+-comm b c)

```

```agda
theory₃ : ∀ (m n : ℕ) → fib (m + suc n) ≡ fib (suc m) * fib (suc n) + fib m * fib n
theory₃ zero n = begin
  fib (suc n)               ≡⟨ sym (+-identityʳ _) ⟩
  fib (suc n) + zero        ≡⟨ sym (+-identityʳ _) ⟩
  fib (suc n) + zero + zero ∎  
theory₃ (suc m) n = begin
  fib (suc (m + suc n))             ≡⟨ cong fib (sym (+-suc m (suc n))) ⟩
  fib (m + suc (suc n))             ≡⟨ theory₃ m (suc n) ⟩
  fsm * (fsn + fn) + (fm * fsn)     ≡⟨ cong (_+ c) (*-distribˡ-+ fsm fsn fn)  ⟩
  a + b + c                         ≡⟨ +-swap₂ a b c ⟩
  a + (c + b)                       ≡⟨ sym (+-assoc a c b) ⟩
  (a + c) + b                       ≡⟨ cong (_+ b) (sym (*-distribʳ-+ fsn fsm fm)) ⟩
  (fsm + fm) * fsn + fsm * fn       ∎
  where
    fm = fib m
    fn = fib n
    fsm = fib (suc m)
    fsn = fib (suc n)
    a = fsm * fsn
    b = fsm * fn
    c = fm * fsn
```

---

### ∑f²n = fn * fn+1

```

∑fib² : ℕ → ℕ
∑fib² zero   = fib 0 * fib 0
∑fib² 1      = fib 1 * fib 1
∑fib² (2+ n) = ∑fib² (suc n) + fib (2+ n) * fib (2+ n)

_ : ∑fib² zero ≡ zero
_ = refl

_ : ∑fib² 1 ≡ 1
_ = refl

_ : ∑fib² 2 ≡ 2
_ = refl

_ : ∑fib² 3 ≡ 6
_ = refl

-- n       = 0 1 2 3  4 5
-- fib n   = 0 1 1 2  3 5
-- ∑fib n  = 0 1 2 4  7 12
-- ∑fib² n = 0 1 2 6 15 40

theory₄ : ∀ (n : ℕ) → ∑fib² n ≡ fib n * fib (suc n)
theory₄ zero    = refl
theory₄ 1       = refl
theory₄ (2+ n) = begin
  ∑fib² (suc n) + fssn * fssn  ≡⟨ cong (_+ (fssn * fssn)) (theory₄ (suc n)) ⟩
  (fsn * fssn) + (fssn * fssn) ≡⟨ +-comm (fsn * fssn) (fssn * fssn) ⟩
  (fssn * fssn) + (fsn * fssn) ≡⟨ sym (*-distribʳ-+ fssn fssn fsn) ⟩
  (fssn + fsn) * fssn          ≡⟨ *-comm (fssn + fsn) fssn ⟩
  fssn * (fssn + fsn)          ∎
  where
    fn   = fib n
    fsn  = fib (suc n)
    fssn = fib (2+ n)
```

-- (∑fib (suc n)) + (fib (suc (suc n)))

---

### m | n ⇒ fm | fn 

```agda
-- if m divides n, then fm divides fn
--gcd(fm,fn) = fgcd(m,n).
-- theory₄ : ∀ (m n : ℕ) →

-- _ : (m n : ℕ) → 2 | 10
-- _  = ?

```

---

### gcd(fm, fn) = f(gcd(m, n))

```agda
```

---

### fib (2+ (2 * n)) ≡ fib (suc n) * fib (suc n) + 2 * fib (suc n) * fib (n)

This one has a mutual proof `fib 2n + 2` needs the proof of `fib 2n + 1` and vice versa

```

a+b²≡a²+2ab+b² : ∀ (a b : ℕ) → a * a + 2 * a * b + b * b ≡ (a + b) * (a + b)
a+b²≡a²+2ab+b² = solve-∀

theory₅+2 : ∀ (n : ℕ) →  fib (2+  (2 * n)) ≡ fib (suc n) * fib (suc n) + 2 * fib (suc n) * fib n
theory₅+1 : ∀ (n : ℕ) →  fib (suc (2 * n)) ≡ fib (suc n) * fib (suc n) + fib n * fib n

theory₅+1 zero = refl
theory₅+1 (suc n) = 
  begin
    fib (suc (2 * (suc n)))
  ≡⟨ cong (λ v → fib (suc v)) (*-suc 2 n) ⟩
    fib (suc (2 + 2 * n))
  ≡⟨⟩
    fib (2+ (2 * n)) + fib (suc (2 * n))
  ≡⟨ cong₂ (λ v₁ v₂ → v₁ + v₂) (theory₅+2 n) (theory₅+1 n) ⟩
   (fib (suc n) * fib (suc n) + 2 * fib (suc n) * fib n) + (fib (suc n) * fib (suc n) + fib n * fib n)
  ≡⟨ (rearrange (fib (suc n)) (fib n)) ⟩
   (fib (suc n) + fib n) * (fib (suc n) + fib n) + fib (suc n) * fib (suc n)
  ∎
  where
    rearrange : ∀ (a b : ℕ) → (a * a + 2 * a * b) + (a * a + b * b) ≡ (a + b) * (a + b) + a * a
    rearrange = solve-∀

theory₅+2 zero = refl
theory₅+2 (suc n) = 
  begin
    fib (2+ (2 * (suc n)))
  ≡⟨ cong (λ v → fib (2+ v)) (*-suc 2 n) ⟩
    fib (2+ (2 + 2 * n))
  ≡⟨⟩
    (fib (2 + 2 * n) + fib (suc (2 * n))) + fib (2+ (2 * n))
  ≡⟨ cong₂ (λ v₁ v₂ → v₂ + v₁ + v₂) (theory₅+1 n) (theory₅+2 n) ⟩
    (fib (suc n) * fib (suc n) + 2 * fib (suc n) * fib n) + (fib (suc n) * fib (suc n) + fib n * fib n) + (fib (suc n) * fib (suc n) + 2 * fib (suc n) * fib n)
  ≡⟨ (rearrange (fib (suc n)) (fib n)) ⟩
    (fib (suc n) + fib n) * (fib (suc n) + fib n) + 2 * (fib (suc n) + fib n) * fib (suc n)
  ∎

  where
    rearrange : ∀ (a b : ℕ) → (a * a + 2 * a * b) + (a * a + b * b) + (a * a + 2 * a * b) ≡ (a + b) * (a + b) + 2 * (a + b) * a
    rearrange = solve-∀
```

---

### fib (2+ (2 * n)) ≡ fib (2+ n) * fib (2+ n) - fib n * fib n

---

### fib (2+ (m + n)) ≡ fib (suc n) * fib (suc m) + fib (suc n) * fib m + fib n * fib (suc m)

## References

1. https://github.com/gallais/potpourri/blob/main/agda/papers/fibonacci/Fib.agda

