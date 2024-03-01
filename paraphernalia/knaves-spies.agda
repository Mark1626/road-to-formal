module paraphernalia.knaves-spies where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂;
  Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Isomorphism using (_⇔_)

-- Knight and Knaves variant
-- https://math.stackexchange.com/questions/2400914/why-do-i-keep-running-into-contradictions-in-this-problem-knights-and-knaves-va

-- There is an island inhabited by two tribes, a tribe of Knaves (who always lie) and Spies (who lie to Knaves but tell the truth to other Spies).

data Person : Set where
  knave : Person
  spy   : Person

says : Person → Person → Set → Set
says knave _   p = ¬ p
says spy knave p = ¬ p
says spy spy   p = p

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬a a = ¬a a

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

-- Knave can never say two valid propositions together
knave-×-elim : ∀ {p : Person} {A B : Set}
  → (A × B) → ¬ (says knave p (A × B))
knave-×-elim = λ a×b ¬a×b → ¬-elim ¬a×b a×b

-- 𝐴 says to 𝐵 : 𝐹 is a Spy, 𝐶 is a Knave.
-- 𝐵 says to 𝐶 : If 𝐷 is a Knave, then so is 𝐸
-- 𝐶 says to 𝐷 : If 𝐴 is a Knave, then 𝐹 is a Spy
-- 𝐷 says to 𝐸 : Either 𝐹 is a Spy, or 𝐴 is a Knave

-- Determine which of the persons 𝐴, 𝐵, 𝐶, 𝐷 and 𝐸
-- are Spies, and which are Knaves.

data Solution₁ : Set where
  soln₁ : (A : Person) → (B : Person)
    → (C : Person) → (D : Person)
    → (E : Person) → (F : Person)
    → (says A B ((F ≡ spy) × (C ≡ knave)))
    → (says B C ( ((D ≡ knave) × (E ≡ knave))))
    → (says C D (((A ≡ knave) × (F ≡ spy))))
    → (says D E ((F ≡ spy) ⊎ (A ≡ knave)))
    → Solution₁

-- Trying with Agda's auto solver

-- Assume A ≡ spy × B ≡ spy
-- soln₁ spy spy ? ? ? ? ? ? ? ?

-- C-a on hole on stmt₁ populated that F ≡ spy
-- soln₁ spy spy knave ? ? spy ⟨ refl , refl ⟩ ? ? ?

-- C-a on hole stmt₄ populated that C ≡ knave, D ≡ spy, E ≡ spy
-- soln₁ spy spy knave spy spy spy ⟨ refl , refl ⟩ ? ? (inj₁ refl)

-- The statements stmt₂ and stmt₃ are to be filled
-- 

_ : Solution₁
_ = soln₁ spy spy knave spy spy spy
  ⟨ refl , refl ⟩ (λ()) (λ()) (inj₁ refl)

-- Spies - A B D E F
-- Knave - C

---

-- The Stack overflow response had three possibilites

-- Assume A ≡ spy × B ≡ knave

-- Using the Auto solver on hole of stmt₄
-- soln₁ spy knave ? spy spy spy ? ? ? (inj₁ refl)

-- The auto solver can find a solution, let's populate the hole of

_ : Solution₁
_ = soln₁ spy knave knave spy knave knave
  (λ()) (λ()) (λ()) λ{ (inj₁ ()) ; (inj₂ ())}

-- Spies - A D
-- Knave - B C E F

_ : Solution₁
_ = soln₁ spy knave spy spy knave knave
  (λ()) {!!} ⟨ {!!} , {!!} ⟩ λ{ (inj₁ x) → {!!} ; (inj₂ y) → {!!}}

