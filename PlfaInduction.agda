module PlfaInduction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- dimostrazione associatività _+_ con induzione

{-
-------------------------------
(zero + n) + p ≡ zero + (n + p)


(m + n) + p ≡ m + (n + p)
-------------------------------
(suc m + n) + p ≡ suc m + (n + p)

-}

+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩ -- come si spiega?
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- dimostrazione commutatività di _+_ per induzione

-- primo lemma
-- abbiamo già id a sinistra, ora dobbiamo provare id a destra

+-identityᴿ : ∀ (m : ℕ) -> m + zero ≡ m
+-identityᴿ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityᴿ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityᴿ m) ⟩
    suc m
  ∎

-- secondo lemma: suc
-- m + suc n ≡ suc (m + n)
+-suc : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc(suc(m + n))
  ≡⟨⟩
    suc(suc m + n)
  ∎

-- dimostrazione finale

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityᴿ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc(m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc(n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                         =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl


+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl


+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- | è per riscrivere con 2 equazioni (seguono l'ordine)
-- esercizi

-- swap ==> m + (n + p) ≡ n + (m + p)

+-swap : ∀ (m n p : ℕ) -> m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym(+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎
