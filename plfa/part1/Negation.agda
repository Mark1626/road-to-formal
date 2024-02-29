module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; z<s; s<s)
--open import Data.Nat.Properties
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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

---

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s≤s n<n) = <-irreflexive n n<n

infix 4 _≮_
_≮_ : ∀ (m n : ℕ) → Set
m ≮ n = ¬ (m < n)

sm≡sn→m≡n : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
sm≡sn→m≡n refl = refl

m≢n→sm≢sn : ∀ {m n : ℕ} → m ≢ n → suc m ≢ suc n
m≢n→sm≢sn m≢n = λ sm≡sn → m≢n (sm≡sn→m≡n sm≡sn)

m≮n→sm≮sn : ∀ {m n : ℕ} → m ≮ n → suc m ≮ suc n
m≮n→sm≮sn m≮n = λ{ (s<s m<n) → m≮n m<n}

trichotomy : ∀ (m n : ℕ)
  → (m < n × m ≢ n × n ≮ m)
  ⊎ (m ≮ n × m ≡ n × n ≮ m)
  ⊎ (m ≮ n × m ≢ n × n < m)
trichotomy zero zero = inj₂ (inj₁ ⟨ (λ()) , ⟨ refl , (λ()) ⟩ ⟩)
trichotomy zero (suc n) = inj₁ ⟨ z<s , ⟨ (λ()) , (λ()) ⟩ ⟩
trichotomy (suc m) zero = inj₂ (inj₂ ⟨ (λ ()) , ⟨ (λ ()) , s≤s z≤n ⟩ ⟩)
trichotomy (suc m) (suc n) with trichotomy m n
... | inj₁ ⟨ m<n , ⟨ m≢n , n≮m ⟩ ⟩ = inj₁ ⟨ (s≤s m<n) , ⟨ m≢n→sm≢sn m≢n , m≮n→sm≮sn n≮m ⟩ ⟩
... | inj₂ (inj₁ ⟨ m≮n , ⟨ refl , n≮m ⟩ ⟩) = inj₂ (inj₁ ⟨ (m≮n→sm≮sn m≮n) , ⟨ refl , (m≮n→sm≮sn n≮m) ⟩ ⟩)
... | inj₂ (inj₂ ⟨ m≮n , ⟨ m≢n , n<m ⟩ ⟩) = inj₂ (inj₂ ⟨ (m≮n→sm≮sn m≮n) , ⟨ m≢n→sm≢sn m≢n , s≤s n<m ⟩ ⟩)

---

⊎-dual-× : ∀ {A B C : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to      = λ{ f → ⟨ (λ a → f (inj₁ a)) , (λ b → f (inj₂ b)) ⟩}
    ; from    = λ{ ⟨ fst , snd ⟩ → [ fst , snd ]}
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ g → refl }
    }

-- Classical Logic

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ λ x → k (inj₁ x))

em-→-¬¬-elim : (∀ {A : Set} → A ⊎ ¬ A)
  → (∀ {A : Set} → ¬ ¬ A → A)
em-→-¬¬-elim a⊎¬a ¬¬a with a⊎¬a
...            | inj₁ a  = a
...            | inj₂ ¬a = ⊥-elim (¬¬a ¬a)

em-→-peirce : (∀ {A : Set} → A ⊎ ¬ A)
  → (∀ {A B : Set} → ((A → B) → A) → A)
em-→-peirce a⊎¬a [a→b]→a with a⊎¬a
... | inj₁ a = a
... | inj₂ ¬a = [a→b]→a λ a → ⊥-elim (¬a a)
