# Continuous Fractions

## References

1. https://pi.math.cornell.edu/~gautam/ContinuedFractions.pdf
2. https://r-knott.surrey.ac.uk/Fibonacci/cfINTRO.html
3. https://perl.plover.com/classes/cftalk/TALK/

```
module cf where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
  using (Acc; acc; <′-Rec; <′-recBuilder; <-wellFounded-fast)
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.List
open import Data.Nat.GCD

open import Relation.Binary.Definitions using (tri<; tri>; tri≈; Symmetric)

open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_; _≢_; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
```

## Definition

```
record CF : Set where
  constructor cf

  field
    repr : List ℕ

cfprepℕ : ℕ → CF → CF
cfprepℕ n c = cf ((n ∷ []) ++ CF.repr c)

fromℕ : ℕ → CF
fromℕ n = cf (n ∷ [])

```

### Usage

```
_ : CF
_ = cf (1 ∷ [])

_ : CF
_ = cf (1 ∷ 2 ∷ 1 ∷ [])
```

```
-- euclid-gcd from Data.Nat.GCD modified to create ContFrac

fromℚ′ : ∀ m n → Acc _<_ m → n < m → CF
fromℚ′ zero            zero  _         _ = cf ([])
fromℚ′ (suc zero)      zero  _         _ = cf ([])
fromℚ′ m@(suc (suc _)) zero  _         _ = cf (m ∷ [])
fromℚ′ m n@(suc _) (acc rec) n<m = cfprepℕ (m / n) (fromℚ′ n (m % n) (rec n<m) (m%n<n m n))

-- TODO: Replace with ℚ from Data.Rational
fromℚ : ℕ → ℕ → CF
fromℚ m n with <-cmp m n
... | tri< m<n _ _   = cfprepℕ 0 (fromℚ′ n m (<-wellFounded-fast n) m<n)
... | tri≈ _   _ _   = cf (1 ∷ [])
... | tri> _   _ n<m = fromℚ′ m n (<-wellFounded-fast m) n<m
```

### Usage

```
_ : gcd 5 15 ≡ 5
_ = P.refl

_ : fromℚ 2 1 ≡ cf (2 ∷ [])
_ = P.refl

_ : fromℚ 43 19 ≡ cf (2 ∷ 3 ∷ 1 ∷ 4 ∷ [])
_ = P.refl

_ : fromℚ 19 43 ≡ cf (0 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ [])
_ = P.refl

```

