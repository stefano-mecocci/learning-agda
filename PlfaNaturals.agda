module PlfaNaturals where

-- Comandi Agda (estensione VS code)
-- Ctrl+c,Ctrl-l controllo il file

-- regole di inferenza
-- composte di eventuali ipotesi e conclusione
{-
  --------
  zero : ℕ  

  m : ℕ
  ---------
  suc m : ℕ 
-}

{- 
- ℕ è un datatype
- zero e suc sono costruttori
- Set è un tipo di dato
- con data si dà una def. induttiva
-}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

-- Un pragma è un tipo speciale di commento
-- qui ci permette di scrivere i numeri naturali come in altri linguaggi
{-# BUILTIN NATURAL ℕ #-}

{-
Con import posso importare altri moduli (es. stdlib) e con as gli assegno un alias.
Tutto ciò compreso dopo using fra parentesi viene importato nello scope.
-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

{-
_x_ operatore infisso
_x  operatore postfisso
x_  operatore prefisso

Usiamo = per le def. e ≡ per le asserzioni
Con _ indichiamo il "dummy name" una variabile usabile
sempre ed ovunque. L'autore ha il dovere di scrivere le equazioni in senso logico per il lettore.
-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- proposizione e dimostrazione
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

-- tutto ciò che sappiamo naturali è definito in Dat.Nat

-- MOLTIPLICAZIONE (grazie all'addizione)

_*_ : ℕ -> ℕ -> ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    12
  ∎

-- SOTTRAZIONE NATURALE (monus)

_∸_ : ℕ -> ℕ -> ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- precedenza degli operatori
-- infixl = associatività a sinistra
-- infixr = associatività a destra
-- infix  = associatività da chiarire con parentesi (disambiguare)
infixl 6  _+_  _∸_
infixl 7  _*_

-- ESERCIZI

-- esponenziale (grazie alla moltiplicazione)

_^_ : ℕ -> ℕ -> ℕ
m ^ zero = suc zero
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    81
  ∎