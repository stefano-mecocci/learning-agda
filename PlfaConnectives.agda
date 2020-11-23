module PlfaConnectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import PlfaIsomorphism using (_≃_; extensionality)

{-
logica proposizionale intuizionista
parte della matematica costruttiva che "assiomatizza" il ragionamento
ragionamento costruttivo = prova come costruzione

logica di MD e ML è logica classica

esistono varie formalizzazioni della logica intuizionista

Deduzione naturale (Gentzen) alias NJ
niente assiomi

and = congiunzione = ∧ = \and 
-}

{-
  A   B  A ∧ B  A ∧ B
  -----  -----  -----
  A ∧ B  A      B

  la congiunzione è il prodotto cartesiano
-}

-- ₁ si scrive \_1
-- × si scrive \times

-- prodotto cartesiano ("and nella categoria degli insiemi")
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

-- prima proiezione
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

-- seconda proiezione
proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

{-
Interpretando A ∧ B ⇔ B ∧ A come A ∧ B |- B ∧ A in NJ

    A ∧ B       A ∧ B
∧E₂ -----   ∧E₁ -----
      B           A
  ∧I ---------------
         B ∧ A

derivazione aperta, albero di derivazione in NJ
-}

-- A ∧ B ⇔ B ∧ A è valida in NJ

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from    = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
    }

-- (A ∧ B) ∧ C ⇔ A ∧ (B ∧ C) è NJ

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

-- valore sempre vero, è l'unità del prodotto
data ⊤ : Set where

  tt :
    --
    ⊤
-- ed il solo valore di tipo ⊤ è tt

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

-- ESERCIZI

-- dimostrare A ⇔ B ≃ (A → B) × (B → A)