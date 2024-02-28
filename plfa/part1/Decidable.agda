module plfa.part1.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ x     = true
suc x ≤ᵇ zero  = false
suc x ≤ᵇ suc y = x ≤ᵇ y

T : Bool → Set
T true = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt         = z≤n
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤?  n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no  m≤n = no (¬s≤s m≤n)

--- Exercise

¬n<z : ∀ {n : ℕ} → ¬ (n < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m     <? zero   = no ¬n<z
zero  <? suc n  = yes z<s
suc m <? suc n with m <? n
... | yes m<n = yes (s<s m<n)
... | no  m<n = no  (¬s<s m<n)

---

¬z≡n : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡n ()

¬m≡z : ∀ {m : ℕ} → ¬ (suc m ≡ zero)
¬m≡z ()

s≡s : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
s≡s refl = refl 

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero  = yes refl
zero ≡ℕ? suc n = no ¬z≡n
suc m ≡ℕ? zero = no ¬m≡z
suc m ≡ℕ? suc n  with m ≡ℕ? n
... | yes m≡n = yes (s≡s m≡n)
... | no  m≡n = no (¬s≡s m≡n)

---

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y}

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
_     ∨ true  = true
false ∨ false = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y}

not : Bool → Bool
not true  = false
not false = true

¬-? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬-? (yes x) = no (¬¬-intro x)
¬-? (no ¬x) = yes ¬x

_⊃_ : Bool → Bool → Bool
_     ⊃ true  = true
false ⊃ _     = true
true  ⊃ false = false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y = yes (λ _ → y)
no ¬x →-dec _     = yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y = no  (λ f → ¬y (f x))
