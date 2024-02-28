module x+distributive where

-- Trying to prove *+distribute
-- From https://www.reddit.com/r/agda/comments/r3aios/how_far_can_i_automate/

open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Nat.Properties

-- *+distributive x y z = *-distribˡ-+ x y z

*+distributive : ∀ (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
*+distributive x zero z = refl
*+distributive x (suc y) z = 
  begin
    (suc y + z) * x
  ≡⟨⟩
    x + (y + z) * x
  ≡⟨ cong (x +_) (*+distributive x y z) ⟩
    x + (y * x + z * x)
  ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩
    x + y * x + z * x
  ≡⟨⟩
    suc y * x + z * x
  ∎
