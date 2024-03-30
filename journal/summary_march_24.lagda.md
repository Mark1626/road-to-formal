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

## 30-03-24

- I found this book on proofs using lean [Math2001](https://hrmacbeth.github.io/math2001)
- Wanted to see if I can use Agda for it's exercises
- The first exercise in Math2001 had used a ring to rearrange eqn, I found that Agda also has ring solvers
- This that might seem trivial at first like `(a+b)²` can involve a lot of rearranging, this can be automatically 
solved with a ring solver.
- Math2001 also had Brahmagupta's id. This bring's back memories, I've used the Chakravala algorithm from Bhaskara for 
solving Pell's equation before. Brahmagupta's identity is related to it as it generalizes the idea used by Bhaskara

```
a+b²≡a²+2ab+b² : ∀ (a b : ℕ) → a * a + 2 * a * b + b * b ≡ (a + b) * (a + b)
a+b²≡a²+2ab+b² = solve-∀

module integer-scenario where
  open import Data.Integer
  open import Data.Integer.Properties
  open import Data.Integer.Tactic.RingSolver

  brahmagupta-id : ∀ (a b c d n : ℤ) → (a * a + n * b * b) * (c * c + n * d * d) ≡
    (a * c - n * b * d) * (a * c - n * b * d) + n * (a * d + b * c) * (a * d + b * c)
  brahmagupta-id = solve-∀
```

- 

