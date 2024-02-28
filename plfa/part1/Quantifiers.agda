module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality; ∀-extensionality)
open import Function using (_∘_)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (y : A) → C y)
∀-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩}
    ; from    = λ{ ⟨ fst , snd ⟩ → λ x → ⟨ (fst x) , (snd x) ⟩ }
    ; from∘to = λ{ f → refl}
    ; to∘from = λ{ ⟨ fst , snd ⟩ → refl }
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (y : A) → C y) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) = inj₁ ∘ f
⊎∀-implies-∀⊎ (inj₂ g) = inj₂ ∘ g

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× =
  record
    { to      = λ{ f → ⟨ (f aa) , ⟨ (f bb) , (f cc) ⟩ ⟩ }
    ; from    = λ
      {⟨ baa , ⟨ bbb , bcc ⟩ ⟩ → λ
        { aa → baa
        ; bb → bbb
        ; cc → bcc
        }
      }
    ; from∘to = λ{ f → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl}}
    ; to∘from = λ{ g → refl }
    }

-- Existentials

data ∑ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → ∑ A B

∑-syntax = ∑
infix 2 ∑-syntax
syntax ∑-syntax A (λ x → Bx) = ∑[ x ∈ A ] Bx

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = ∑ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  → C
∃-elim f ⟨ x , y ⟩ = f x y


∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      = λ{f → λ{ ⟨ x , y ⟩ → f x y}}
    ; from    = λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      = λ
      { ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
      ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩
      }
    ; from    = λ
      { (inj₁ ⟨ A , BA ⟩) → ⟨ A , inj₁ BA ⟩
      ; (inj₂ ⟨ A , CA ⟩) → ⟨ A , inj₂ CA ⟩
      }
    ; from∘to = λ
      { ⟨ x , inj₁ Bx ⟩ → refl
      ; ⟨ x , inj₂ Cx ⟩ → refl
      }
    ; to∘from = λ
      { (inj₁ ⟨ A , BA ⟩) → refl
      ; (inj₂ ⟨ A , CA ⟩) → refl
      }
    }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ A , ⟨ BA , CA ⟩ ⟩ = ⟨ ⟨ A , BA ⟩ , ⟨ A , CA ⟩ ⟩

∃-⊎ : {B : Tri → Set} → (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
    { to      = λ
      { ⟨ aa , x ⟩ → inj₁ x
      ; ⟨ bb , y ⟩ → inj₂ (inj₁ y)
      ; ⟨ cc , z ⟩ → inj₂ (inj₂ z)
    }
    ; from    = λ
      { (inj₁ x) → ⟨ aa , x ⟩
      ; (inj₂ (inj₁ y)) → ⟨ bb , y ⟩
      ; (inj₂ (inj₂ z)) → ⟨ cc , z ⟩
      }
    ; from∘to = λ
      { ⟨ aa , x ⟩ → refl
      ; ⟨ bb , y ⟩ → refl
      ; ⟨ cc , z ⟩ → refl
      }
    ; to∘from = λ
      { (inj₁ x) → refl
      ; (inj₂ (inj₁ y)) → refl
      ; (inj₂ (inj₂ z)) → refl
      }
    }

---

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}  → even n → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (     m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} → odd n  → ∃[ m ] ( 1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc e) with even-∃ e
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

---

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc x , refl ⟩ = even-suc (∃-odd ⟨ x , refl ⟩)

∃-odd ⟨ x , refl ⟩ = odd-suc (∃-even ⟨ x , refl ⟩)

---

-- ∃′-even : ∀ {n : ℕ} → ∃[ m ] (2 * m     ≡ n) → even n
-- ∃′-odd  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n

-- ∃′-even ⟨ zero , refl ⟩ = even-zero
-- ∃′-even ⟨ suc x , refl ⟩ = even-suc (∃′-odd ⟨ x , {!!} ⟩)

-- ∃′-odd x = {!!}

--

∃-+-≤ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤ {zero} ⟨ zero , refl ⟩ = z≤n
∃-+-≤ {zero} ⟨ suc x , refl ⟩ = z≤n
∃-+-≤ {suc x} ⟨ zero , refl ⟩ = s≤s (∃-+-≤ ⟨ zero , refl ⟩)
∃-+-≤ {suc x} ⟨ suc y , refl ⟩ = s≤s (∃-+-≤ ⟨ suc y , sym (+-suc y x) ⟩)

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      = λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩}
    ; from    = λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to = λ{ ¬∃xy → refl }
    ; to∘from = λ{ ∀¬xy → refl}
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x) → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ xBx = ¬Bx (xBx x)
