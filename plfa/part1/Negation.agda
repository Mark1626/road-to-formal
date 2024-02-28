module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
  → ¬ ¬ A
¬¬-intro x = λ{¬x → ¬x x}

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s≤s n<n) = <-irreflexive n n<n

⊎-dual-× : ∀ {A B C : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to      = λ{ f → ⟨ (λ a → f (inj₁ a)) , (λ b → f (inj₂ b)) ⟩}
    ; from    = λ{ ⟨ fst , snd ⟩ → [ fst , snd ]}
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ g → refl }
    }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ x → x (inj₂ λ{A → x (inj₁ A)})

em-→-¬¬-elim : (∀ {A : Set} → A ⊎ ¬ A)
  → (∀ {A : Set} → ¬ ¬ A → A)
em-→-¬¬-elim a⊎¬a ¬¬a with a⊎¬a
...            | inj₁ a  = a
...            | inj₂ ¬a = ⊥-elim (¬¬a ¬a)
