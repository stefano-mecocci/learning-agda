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

congiunzione = ∧ = \and 
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

-- "truth is unit"
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

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ =
  record
    { to      = λ{ ⟨ x , tt ⟩ → x }
    ; from    = λ{ x → ⟨ x , tt ⟩ }
    ; from∘to = λ{ ⟨ x , tt ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

infixr 2 _×_

-- disgiunzione
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

-- distruttori sulla sinistra e costruttori sulla destra
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

infixr 1 _⊎_

-- "false is empty"
data ⊥ : Set where

-- uso dell'absurd pattern
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- "implication is function"
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

-- ESERCIZI

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ { (inj₁ a) → (inj₂ a) ; (inj₂ b) → (inj₁ b) }
    ; from = λ { (inj₁ a) → (inj₂ a) ; (inj₂ b) → (inj₁ b) }
    ; from∘to = λ { (inj₁ a) → refl ; (inj₂ b) → refl }
    ; to∘from = λ { (inj₁ a) → refl ; (inj₂ b) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ { (inj₁ (inj₁ a)) → inj₁ a
             ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
             ; (inj₂ c) → inj₂ (inj₂ c) }
    ; from = λ { (inj₁ a) → inj₁ (inj₁ a)
               ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
               ; (inj₂ (inj₂ c)) → inj₂ c }
    ; from∘to = λ { (inj₁ (inj₁ a)) → refl
                  ; (inj₁ (inj₂ b)) → refl
                  ; (inj₂ c) → refl }
    ; to∘from = λ { (inj₁ a) → refl
                  ; (inj₂ (inj₁ b)) → refl
                  ; (inj₂ (inj₂ c)) → refl }
    }

⊥-identityˡ : ∀ {B : Set} → ⊥ ⊎ B ≃ B
⊥-identityˡ =
  record
    { to = λ{ (inj₂ b) → b }
    ; from = λ{ b → inj₂ b }
    ; from∘to = λ{ (inj₂ b) → refl }
    ; to∘from = λ{ b → refl }
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to = λ{ (inj₁ a) → a }
    ; from = λ{ a → inj₁ a }
    ; from∘to = λ{ (inj₁ a) → refl }
    ; to∘from = λ{ a → refl }
    }
