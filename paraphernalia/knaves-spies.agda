module paraphernalia.knaves-spies where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product using (_×_; proj₁; proj₂;
  Σ; Σ-syntax; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty
open import Function
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

-- Statements If A then B

if-⊤-implies-× : ∀ {A B : Set} → A → (A → B) → (A × B)
if-⊤-implies-× a x = ⟨ a , x a ⟩

if-⊥-implies : ∀ {A B : Set} → ¬ A → (A → B) → ⊥
if-⊥-implies ¬a a→b = {!()!}

data Solution₁ : Set where
  soln₁ : (A : Person) → (B : Person)
    → (C : Person) → (D : Person)
    → (E : Person) → (F : Person)
    → (says A B ((F ≡ spy) × (C ≡ knave)))
    → (says B C ((D ≡ knave) × (E ≡ knave)))
    → (says C D ((A ≡ knave) × (F ≡ spy)))
    → (says D E ((F ≡ spy) ⊎ (A ≡ knave)))
    → Solution₁

absurd : ⊥ → spy ≡ knave
absurd ()

elim-absurd₁ : spy ≡ knave → ⊥
elim-absurd₁ ()

elim-absurd₂ : knave ≡ spy → ⊥
elim-absurd₂ ()

elim-absurd→ : ((spy ≡ knave) → (spy ≡ knave)) → (spy ≡ knave) → ⊥
elim-absurd→ x ⊥spy≡knave = elim-absurd₁ (x ⊥spy≡knave)

-- contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
-- contraposition f ¬y ¬x = ¬y (f x)

-- Trying with Agda's auto solver

-- Assume A ≡ spy × B ≡ spy
-- soln₁ spy spy ? ? ? ? ? ? ? ?

-- C-a on hole on stmt₁ populated that F ≡ spy
-- soln₁ spy spy knave ? ? spy ⟨ refl , refl ⟩ ? ? ?

-- C-a on hole stmt₄ populated that C ≡ knave, D ≡ spy, E ≡ spy
-- soln₁ spy spy knave spy spy spy ⟨ refl , refl ⟩ ? ? (inj₁ refl)

-- The statements stmt₂ and stmt₃ are to be filled
-- 

-- ((D ≢ knave) ⊎ ((D ≡ knave) × (E ≡ knave))))
-- _ : Solution₁
-- _ = soln₁ spy spy knave spy spy spy
--   ⟨ refl , refl ⟩
--  (λ{ (inj₁ x) → contradiction {!!} x })
--   (λ{ (inj₁ x) → {!!}})
--   (inj₁ refl)

answer₁ : Solution₁
answer₁ = soln₁ spy spy knave spy spy spy
  ⟨ refl , refl ⟩
  (λ())
  (λ())
  (inj₁ refl)

-- Spies - A B D E F
-- Knave - C

---

-- The Stack overflow response had three possibilites

-- Assume A ≡ spy × B ≡ knave

-- Using the Auto solver on hole of stmt₄
-- soln₁ spy knave ? spy spy spy ? ? ? (inj₁ refl)

-- The auto solver can find a solution, let's populate the hole of

answer₂ : Solution₁
answer₂ = soln₁ spy knave knave spy knave knave
  (λ())
  (λ())
  (λ())
  λ{ (inj₁ ()) ; (inj₂ ())}

-- Spies - A D
-- Knave - B C E F

-- 𝐴 says to 𝐵 : 𝐹 is a Spy, 𝐶 is a Knave.
-- 𝐵 says to 𝐶 : If 𝐷 is a Knave, then so is 𝐸
-- 𝐶 says to 𝐷 : If 𝐴 is a Knave, then 𝐹 is a Spy
-- 𝐷 says to 𝐸 : Either 𝐹 is a Spy, or 𝐴 is a Knave

-- Unable to prove statement₃ because if made (A → B) as (A × B)
answer₃ : Solution₁
answer₃ = soln₁ spy knave spy spy knave knave
  (λ())
  (λ())
  ⟨ {!!} , {!!} ⟩
  λ{ (inj₁ x) → elim-absurd₂ x ; (inj₂ y) → elim-absurd₁ y}
