module PlfaIsomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

{-
  nota: λ si scrive \Gl
        ↦ si scrive \mapsto
        ∘ si scrive \o

  (λ{P → M; Q → N}) a = Mσ se a = Pσ
                      = Nσ se a = Qσ
                      altrimenti indefinito

  es.

  (λ{ ⟨x, y⟩ -> x }) ⟨ M, N ⟩ = xσ = M 
  
  dove σ = {x ↦ M, y ↦ N}

  Inoltre

  λx -> N ≡ λ{x -> N}
-}

-- composizione
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

-- un record è come una dichiarazione con data ed un solo costruttore
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

infix 0 _≃_

-- nota: ≃ si scrive \~ -
-- Essa è una relazione binaria d'equivalenza

-- evita di scrivere _≃_.field (basta solo field)
open _≃_

-- riflessività
≃-refl : ∀ {A : Set}
    ------
  → A ≃ A
≃-refl =
  record
    { to      = λ x → x
    ; from    = λ y → y
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B =    -- una variabile di tipo A ≃ B
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to      = to B≃C ∘ to A≃B
    ; from    = from A≃B ∘ from B≃C
    ; from∘to = λ x → 
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x))) -- per la def. di composizione
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)                      -- per la def. di _≃_
        ≡⟨ from∘to A≃B x ⟩
          x                                         -- per la def. di _≃_
        ∎
    ; to∘from = λ y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎
    }

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g