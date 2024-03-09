# Summary - Feb 2024

<--
```agda
module summary where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

```
-->

I managed to finish part 1 of PLFA. I wanted to see if I can
apply the idea of *Proposition as Types* for
a logical puzzles as I've tried using formal
solvers Z3 for puzzles before.

## Knight and Knaves

Knights and Knaves had been tried out in Agda before in this article, so I
thought of starting with it
https://pwparchive.wordpress.com/2012/09/06/logical-puzzles-in-agda/

I was new to Intuitionistic logic and the
difference between a negation in Classical logic was initially not evident
until I encountered the my first scenario of double negation.

```agda
data Person₁ : Set where
  knight : Person₁
  knave : Person₁

says : Person₁ → Set → Set
says knight p = p
says knave  p = ¬ p

```

> Z3 examples for Knights and Knaves used to model it with Boolean

I tried out some examples of my own after this

**Example 1**

```agda
-- From https://philosophy.hku.hk/think/logic/knights.php
-- Puzzle #1
-- You meet two inhabitants: Zoey and Mel. Zoey tells you that Mel is a knave. Mel says, “Neither Zoey nor I are knaves.”

elim-≢ : ¬ (knight ≡ knave)
elim-≢ = λ ()

data Solution₃ : Set where
    soln₃ : (Zoey : Person₁) → (Mel : Person₁) →
      (says Zoey (Mel ≡ knave)) →
      (says Mel ((¬ (Zoey ≡ knave)) × (¬ (Mel ≡ knave)))) →
      Solution₃

-- Manual interactive proof

_ : Solution₃
_ = soln₃ knight knave
  refl
  λ{ ⟨ knv≢kni , knv≢knv ⟩ → ⊥-elim (knv≢knv refl)}

```

**Example 2**

-- You meet two inhabitants: Peggy and Zippy. Peggy tells you that “of Zippy and I, exactly one is a knight'. Zippy tells you that only a knave would say that Peggy is a knave.


```agda
data Solution₄ : Set where
  soln₄ : (Peggy : Person₁) → (Zippy : Person₁)
    → (says Peggy ((Zippy ≡ knight × Peggy ≢ knight) ⊎ (Zippy ≢ knight × Peggy ≡ knight)))
    → (says Zippy (says knave (Peggy ≡ knave)))
    → Solution₄

_ : Solution₄

_ = soln₄ knave knave
  (λ{ (inj₁ ()) ; (inj₂ ())})
  (λ knv≢knv → ⊥-elim (knv≢knv refl))

```

**Example 3**

```agda
-- There are two people, A and B. A says "We are both Knaves"

data Solution₅ : Set where
  soln₅ : (A : Person₁) → (B : Person₁)
    → (says A ((A ≡ knave) × (B ≡ knave)))
    → Solution₅

_ : Solution₅
_ = soln₅ knave knight λ()


```

## Knaves and Spies

This was a variant that I found from a StackExchange question.
https://math.stackexchange.com/questions/2400914/why-do-i-keep-running-into-contradictions-in-this-problem-knights-and-knaves-va


```agda
data Person₂ : Set where
  knave₂ : Person₂
  spy₂   : Person₂

says₂ : Person₂ → Person₂ → Set → Set
says₂ knave₂ _    p = ¬ p
says₂ spy₂ knave₂ p = ¬ p
says₂ spy₂ spy₂   p = p
```

This one was a bit more tricky, as 3 out of 4 cases of
says are negations.

**The problem**

```
-- stmt₁ 𝐴 says to 𝐵 : 𝐹 is a Spy, 𝐶 is a Knave.
-- stmt₂ 𝐵 says to 𝐶 : If 𝐷 is a Knave, then so is 𝐸
-- stmt₃ 𝐶 says to 𝐷 : If 𝐴 is a Knave, then 𝐹 is a Spy
-- stmt₄ 𝐷 says to 𝐸 : Either 𝐹 is a Spy, or 𝐴 is a Knave

-- Determine which of the persons 𝐴, 𝐵, 𝐶, 𝐷 and 𝐸
-- are Spies, and which are Knaves.
```

I ran into a far bit of trouble trying to model the implications
statements stmt₂, stmt₃.

One, I tried just using it as `(D ≡ knave) → (E ≡ knave)`. Proving the negation
of this did not work.

Two, then I tried to model it as `(D ≢ knave) ⊎ ((D≡knave) → (E ≡ knave))`
which also did not work as for the union I had to both `inj` and I was not
able to prove `inj₂`.

Three, I wanted to use IAD `(A → B)` as `(¬A ⊎ B)`, this would require to
postulate the law of excluded middle `A ⊎ ¬ A`. Still when I had to match
the cases I ran into proving issues proving both `inj₁` and `inj₂`. 

I later went with this theory. When A, `(A → B)` implies `(A × B)`, I was
able to prove this and use it to solve the puzzle. When ¬A, I was not
able to find a solution.

```
if-⊤-implies-× : ∀ {A B : Set} → A → (A → B) → (A × B)
if-⊤-implies-× a x = ⟨ a , x a ⟩

postulate
  if-⊥-implies : ∀ {A B : Set} → ¬ A → (A → B) → ⊥
```

```agda
data Solution₁ : Set where
  soln₁ : (A : Person₂) → (B : Person₂)
    → (C : Person₂) → (D : Person₂)
    → (E : Person₂) → (F : Person₂)
    → (says₂ A B ((F ≡ spy₂) × (C ≡ knave₂)))
    → (says₂ B C ((D ≡ knave₂) × (E ≡ knave₂)))
    → (says₂ C D ((A ≡ knave₂) × (F ≡ spy₂)))
    → (says₂ D E ((F ≡ spy₂) ⊎ (A ≡ knave₂)))
    → Solution₁
```

```agda
answer₁ : Solution₁
answer₁ = soln₁ spy₂ spy₂ knave₂ spy₂ spy₂ spy₂
  ⟨ refl , refl ⟩
  (λ())
  (λ())
  (inj₁ refl)

-- Spies - A B D E F
-- Knave - C
```

```agda
answer₂ : Solution₁
answer₂ = soln₁ spy₂ knave₂ knave₂ spy₂ knave₂ knave₂
  (λ())
  (λ())
  (λ())
  λ{ (inj₁ ()) ; (inj₂ ())}

-- Spies - A D
-- Knave - B C E F

```

```
-- Unable to prove statement₃ because I made (A → B) as (A × B)
-- Maybe could have modelled (A → B) as (¬A ⊎ B)
-- answer₃ : Solution₁
-- answer₃ = soln₁ spy knave spy spy knave knave
--  (λ())
--  (λ())
--  ⟨ {!!} , {!!} ⟩
--  λ{ (inj₁ x) → elim-absurd₂ x ; (inj₂ y) → elim-absurd₁ y}

```

## What's next

1. I will be going through Part 2 of PLFA, as I don't have exposure
to the formalization of Lambda calculus, hence solving part-2 would be useful
2. On the Knaves and Spy puzzle I'm thinking of revisiting it later
3. Start exploring how to model algorithm complexity bounds in Agda.

