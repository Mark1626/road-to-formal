module logic-puzzle where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Nat.Properties

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

-- https://pwparchive.wordpress.com/2012/09/06/logical-puzzles-in-agda/
-- Using standard library rather than defining it here

-- On the day of his arrival, Abercrombie came across three inhabitants, whom we will call A, B and C. He asked A: “Are you a knight or a knave?” A answered, but so indistinctly that Abercrombie could not understand what he said. He then asked B: “What did he say?” B replied: “He said that he is a knave.” At this point, C piped up and said: “Don’t believe that; it’s a lie!”. Was C a knight or a knave?

data Person : Set where
  knight : Person
  knave  : Person

says : Person → Set → Set
says knight p = p
says knave  p = ¬ p

data Solution₀ : Set where
  soln₀ : (a : Person) → (b : Person) → (c : Person) →
    (says b (says a (a ≡ knave))) → (says c (b ≡ knave)) →
    Solution₀


-- Start with solution₀ : Solution₀ = ?
-- The puzzle can be solved with Agda's auto solver
-- by using C-c C-a


solution₀ : Solution₀
solution₀ = soln₀ knight knave knight (λ ()) refl

---

-- Suppose that you visit the Island of Knights and Knaves because you have heard a rumor that there is gold buried there. You meet a native and you wish to find out from him whether there really is gold there, but you don’t know whether he is a knight or a knave. You are allowed to ask him only one question answerable by yes or no. What question would you ask?

Prp : Set₁
Prp = Person → Set

-- If and only if
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

data PredicateTransform : Set₁ where
  predicateTrans : (f : Prp → Prp) →
    ((OldP : Prp) → (p : Person) →
    (OldP p) ⇔ (says p ((f OldP) p))) →
     PredicateTransform

postulate
  elim-¬¬ : {A : Set} → ¬ ¬ A → A

soln : PredicateTransform
soln = predicateTrans f proof
  where f : Prp → Prp
        f q p = says p (q p)
        proof : (A : Prp) → (p : Person) → (A p) ⇔ (says p ((f A) p))
        proof A knight = 
          record
            { to = λ prf → prf
            ; from = λ prf → {!prf!}
            }
        proof A knave = 
          record
            { to = λ prf → λ z → z prf
            ; from = λ prf → elim-¬¬ prf
            }

