# Summary March 2024

- Tried proving fibonnaci identities with induction
- Created a post on r/agda
- Found out that order matters. As an example trying to prove a swap

```agda
test₁ : ∀ (a b c : ℕ) → a + b + c ≡ b + a + c
test₁ a b c = cong (_+ c) (+-comm a b)

test₂ : ∀ (a b c : ℕ) → a + b + c ≡ a + (c + b)
test₂ a b c rewrite +-assoc a b c = cong (a +_) (+-comm b c)
```

