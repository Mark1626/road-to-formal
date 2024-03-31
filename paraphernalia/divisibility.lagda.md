```
open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Nat.DivMod
import Relation.Binary.PropositionalEquality as PEq
open PEq
open PEq.≡-Reasoning
```

```
div-prop₁ : {a b : ℕ} → (a ≡ 2) → (b ≡ 4) → a ∣ b
div-prop₁ {a} {b} a≡2 b≡4 = divides 2 (begin
  b              ≡⟨ b≡4 ⟩
  4              ≡⟨⟩
  2 + 2          ≡⟨ cong (λ v → v + v) (sym a≡2) ⟩
  a + a          ≡⟨ cong (a +_) (sym (+-identityʳ _)) ⟩
  a + (a + zero) ∎)

div-prop₂ : 4 / 2 ≡ 2
div-prop₂ = refl

div-prop₃ : {n : ℕ} → n / 1 ≡ n
div-prop₃ {n} = {!!}

divs-prop₄ : ∀ m n . {{_ : NonZero m }} → n ≡ (m * n) / m
divs-prop₄ m n = {!begin
  n     ≡⟨⟩
  n / 1 ≡⟨ sym (m*n/m*o≡n/o m n 1) ⟩
  (m * n) / (m * 1) ∎!}
  where
    prop₁ : ∀ {m n : ℕ} → m ∣ n * m
    prop₁ {m} {n} = divides n refl
    prop₂ : ∀ {n : ℕ} → n / 1 ≡ n
    prop₂ {n} = {!!}

```

