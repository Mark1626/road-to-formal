module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

infixr 2 _×_

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B)
  → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

data Bool : Set where
  true : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩ = 1
×-count ⟨ true  , bb ⟩ = 2
×-count ⟨ true  , cc ⟩ = 3
×-count ⟨ false , aa ⟩ = 4
×-count ⟨ false , bb ⟩ = 5
×-count ⟨ false , cc ⟩ = 6

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  = λ{ ⟨ x , y ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

open _⇔_

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× =
  record
    { to      = λ{ A⇔B → ⟨ to A⇔B   , from A⇔B ⟩ }
    ; from    = λ{ AB×BA → record { to = proj₁ AB×BA
                                  ; from = proj₂ AB×BA
                                  } }
    ; from∘to = λ{ A⇔B → refl }
    ; to∘from = λ{ AB×BA →
      begin
        ⟨ to record { to = proj₁ AB×BA  ; from = proj₂ AB×BA }
        , from record { to = proj₁ AB×BA ; from = proj₂ AB×BA }
        ⟩
      ≡⟨⟩
        ⟨ proj₁ AB×BA , proj₂ AB×BA ⟩
      ≡⟨ η-× AB×BA ⟩
        AB×BA
      ∎
      }
    }

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

--- Disjunction

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C) → (B → C) → A ⊎ B
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ x) = g x

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infixr 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)  = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ aa)    = 3
⊎-count (inj₂ bb)    = 4
⊎-count (inj₂ cc)    = 5

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = 
  record
    { to      = λ
      { (inj₁ A) → inj₂ A
      ; (inj₂ B) → inj₁ B
      }
    ; from    = λ
      { (inj₁ B) → inj₂ B
      ; (inj₂ A) → inj₁ A
      }
    ; from∘to = λ
      { (inj₁ A⊎B) → refl
      ; (inj₂ B⊎A) → refl
      }
    ; to∘from = λ
      { (inj₁ B⊎A) → refl
      ; (inj₂ A⊎B) → refl
      }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to      = λ
      { (inj₁ (inj₁ A)) →  inj₁ A
      ; (inj₁ (inj₂ B)) →  inj₂ (inj₁ B) 
      ; (inj₂ C) →  inj₂ (inj₂ C)
      }
    ; from    =  λ
      { (inj₁ A) → inj₁ (inj₁ A)
      ; (inj₂ (inj₁ B)) → inj₁ (inj₂ B)
      ; (inj₂ (inj₂ C)) → inj₂ C
      }
    ; from∘to = λ
      { (inj₁ (inj₁ A)) → refl
      ; (inj₁ (inj₂ B)) → refl
      ; (inj₂ C) → refl
      }
    ; to∘from = λ
      { (inj₁ A) → refl
      ; (inj₂ (inj₁ x)) → refl
      ; (inj₂ (inj₂ x)) → refl
      }
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- inj₂ is ⊥ which is not possible
⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
  { to      = λ{ (inj₁ A) → A }
  ; from    = λ{ A → inj₁ A }
  ; from∘to = λ{ (inj₁ A) → refl }
  ; to∘from = λ{ A → refl}
  }

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
  { to      = λ{ (inj₂ A) → A}
  ; from    = λ{ A → inj₂ A }
  ; from∘to = λ{ (inj₂ A) → refl}
  ; to∘from = λ{ A → refl }
  }

→-elim : ∀ {A B : Set}
  → (A → B) → A
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      = λ{ f → λ{ ⟨ A , B ⟩ →  f A B}}
    ; from    = λ{ g → λ { y → λ x → g ⟨ y , x ⟩ }}
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality λ { ⟨ x , y ⟩ → refl } 
    }

→-distrib-⊎ : ∀ {A B C : Set}
  → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ
      { f → ⟨ (λ A → f (inj₁ A)) , ((λ B → f (inj₂ B))) ⟩}
    ; from = λ
      { ⟨ g₁ , g₂ ⟩ → λ
        { (inj₁ A) → g₁ A
        ; (inj₂ B) → g₂ B
        }
      }
    ; from∘to = λ
      { f → extensionality λ
        { (inj₁ A) → refl
        ; (inj₂ B) → refl
        }
      }
    ; to∘from = λ{ ⟨ g₁ , g₂ ⟩ → refl}
    }

→-distrib-× : ∀ {A B C : Set}
  → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩}
    ; from    = λ{ ⟨ g₁ , g₂ ⟩ → λ x → ⟨ (g₁ x) , (g₂ x) ⟩}
    ; from∘to = λ{ f → extensionality λ { x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g₁ , g₂ ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set}
  → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ
      { ⟨ inj₁ A , C ⟩ → inj₁ ⟨ A , C ⟩
      ; ⟨ inj₂ B , C ⟩ → inj₂ ⟨ B , C ⟩
      }
    ; from    = λ
      { (inj₁ ⟨ A , C ⟩) → ⟨ inj₁ A , C ⟩
      ; (inj₂ ⟨ B , C ⟩) → ⟨ inj₂ B , C ⟩
      }
    ; from∘to = λ
      { ⟨ inj₁ A , C ⟩ → refl
      ; ⟨ inj₂ B , C ⟩ → refl
      }
    ; to∘from = λ
      { (inj₁ ⟨ A , C ⟩) → refl
      ; (inj₂ ⟨ B , C ⟩) → refl
      }
    }

⊎-distrib-× : ∀ {A B C : Set}
  → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ
      { (inj₁ ⟨ A , B ⟩) → ⟨ inj₁ A , inj₁ B ⟩
      ; (inj₂ C) → ⟨ (inj₂ C) , (inj₂ C) ⟩
      } 
    ; from    = λ
      { ⟨ inj₁ A , inj₁ B ⟩ → inj₁ ⟨ A , B ⟩
      ; ⟨ inj₁ A , inj₂ C ⟩ → inj₂ C
      ; ⟨ inj₂ C , _ ⟩ → inj₂ C
      }
    ; from∘to = λ
      { (inj₁ ⟨ A , B ⟩) → refl
      ; (inj₂ C) → refl
      }
    }

-- Exercise

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ A , _ ⟩ = inj₁ A
⊎-weak-× ⟨ inj₂ B , C ⟩ = inj₂ ⟨ B , C ⟩

--postulate
--  ⊎-weak-×-distrib : ∀ {A B C : Set}

⊎×-implies-×⊎ : ∀ {A B C D : Set}
  → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ A , B ⟩) = ⟨ (inj₁ A) , (inj₁ B) ⟩
⊎×-implies-×⊎ (inj₂ ⟨ C , D ⟩) = ⟨ (inj₂ C) , (inj₂ D) ⟩
