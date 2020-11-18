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

-- {...} argomenti impliciti
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

-- +-comm m n  per  m + n ≡ n + m
--        z≤n  per  zero ≤ n
-- n è implicito
-- gli argomenti impliciti possono essere resi espliciti
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- anche espliciti con nome è possibile
_ : 1 ≤ 3
_ = (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

infix 4 _≤_

-- inversione
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
≤-refl {suc n} = s≤s ≤-refl -- uguale a suc n ≤ suc n
