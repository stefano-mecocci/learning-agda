module PlfaRelations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

{- 
z≤n --------
    zero ≤ n

    m ≤ n
s≤s -------------
    suc m ≤ suc n

dove z≤n e s≤s sono nomi, evidenze
di zero ≤ n e m ≤ n
-}

-- {...} indica argomenti impliciti
-- questo si chiama "indexed datatype"
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

-- z≤n e s≤s sono nomi di costruttori ed n è implicito

-- uso classico
_ : 2 ≤ 4
_ = s≤s (s≤s (z≤n))

-- gli argomenti impliciti possono essere resi espliciti
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- oppure espliciti con nome è possibile
_ : 1 ≤ 3
_ = (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

infix 4 _≤_

-- inversione: partire da cosa più grandi verso cose più piccole
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

-- riflessività
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- transitività
-- I primi 3 valori sono i parametri
≤-trans : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans zero    _       _       z≤n       _          =  z≤n
≤-trans (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m n p m≤n n≤p)

-- antisimmetria

-- data f = suc applichiamo la congruenza dove
--        m <= n, n <= m
-- ------------------------------
-- suc m <= suc n, suc n <= suc m

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

-- totalità

-- datatype ausiliario con parametri
data Total (m n : ℕ) : Set where
  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

-- proprietà effettiva
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

-- uguale ma usiamo un lemma (funzione locale)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)


-- definiamo la disuguaglianza stretta 

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- ESERCIZI

-- transitività di <
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s       (s<s n<p)         = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- suc m <= n implica m < n
<-if-≤ : ∀ (m n : ℕ)
  → (suc m) ≤ n
  ----------
  → m < n
<-if-≤ zero (suc n) _ = z<s
<-if-≤ (suc m) (suc n) (s≤s sm≤n) = s<s (<-if-≤ m n sm≤n)
