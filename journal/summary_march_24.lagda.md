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

- I found this book on proofs using lean [The Mechanics of Proof](https://hrmacbeth.github.io/math2001)
- Wanted to see if I can use Agda for it's exercises
- The first exercise in Math2001 had used a ring to rearrange eqn, I found that Agda also has ring solvers
- This that might seem trivial at first like `(a+b)²` can involve a lot of rearranging, this can be automatically 
solved with a ring solver.
- Mechanics of Proof also had Brahmagupta's id. This bring's back memories, I've used the Chakravala algorithm from Bhaskara for 
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

## 31-03-24

- Currently swapping between working with ℤ and ℕ is a bit tedious
- The major learning from this book so far is that I have to mix a lot of concepts. In PLFA a chapter was specific to one topic, whereas here in the folliwing example I had to use a ring solver, apply equality inside a manual ≡-reasoning

```
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
```
