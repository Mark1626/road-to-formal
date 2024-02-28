module knight-knaves where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

data Person : Set where
  knight : Person
  knave  : Person

says : Person → Set → Set
says knight p = p
says knave  p = ¬ p

-- From https://pwparchive.wordpress.com/2012/09/06/logical-puzzles-in-agda/

-- On the day of his arrival, Abercrombie came across three inhabitants, whom we will call A, B and C. He asked A: “Are you a knight or a knave?” A answered, but so indistinctly that Abercrombie could not understand what he said. He then asked B: “What did he say?” B replied: “He said that he is a knave.” At this point, C piped up and said: “Don’t believe that; it’s a lie!”. Was C a knight or a knave?


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
            ; from = λ prf → prf
            }
        proof A knave = 
          record
            { to = λ prf → λ z → z prf
            ; from = λ prf → elim-¬¬ prf
            }

--- Some puzzles on my own

-- From https://philosophy.hku.hk/think/logic/knights.php
-- You meet two inhabitants: Zoey and Mel. Zoey tells you that Mel is a knave. Mel says, “Neither Zoey nor I are knaves.”

data Solution₂ : Set where
    soln₂ : (Zoey : Person) → (Mel : Person) →
      (says Zoey (Mel ≡ knave)) →
      (says Mel ((Zoey ≢ knave) ⊎ (Mel ≢ knave))) →
      Solution₂

-- Manual interactive proof

-- _ : Solution₂
-- _ = soln₂ knight knave refl λ{ (inj₁ x) → {!!} ; (inj₂ y) → {!!}}
