module NaturalNumbers where

{-
  Qui N è il datatype che stiamo definendo. Mentre `zero` e `suc` sono i costruttori del datatype.
  Con `data` si dà una definizione induttiva e il tipo è `Set`. I costruttori vanno sempre allineati. È possibile attribuire un significato alla nostra definizione senza ricorrere a circolarità non ammesse.
  In pratica ci dicono:
  - zero è un numero naturale
  - se m è un naturale allora anche suc m è un naturale

  --------
  zero : ℕ

  m : ℕ
  ---------
  suc m : ℕ 

  Ogni regola di inferenza è composta da zero o più sentenze scritte sopra una linea orizzontale, chiamate IPOTESI e una sentenza sotto chiamata CONCLUSIONE. La prima è il caso base, non ha ipotesi ed asserisce che zero è naturale. La seconda è il caso induttivo, ha un'ipotesi e assume che se m è naturale anche suc m lo è.
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

{-
Un pragma è uno speciale tipo di commento che in questo caso ci permette di esprimere i numeri naturali come qualsiasi linguaggio di progrmmazione: es. 2 == suc (suc zero) 
-}

{-# BUILTIN NATURAL ℕ #-}

{- 

La prima riga importa la parte di stdlib Equality con alias Eq. Le altre righe portano tutto ciò che è compreso fra parentesi dopo `using` nello scope (_\==_, refl, ecc.). Inoltre:
_x_ = operatore infisso
x_  = operatore prefisso
_x  = operatore postfisso

-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

{- 
m + n == _+_ m n
La prima riga dice che + prende due argomenti e ne restituisce uno(la stranezza è chiarita dal CURRYING). Se i costruttori appaiono sulla sinistra diciamo di usare il PATTERN MATCHING. Usiamo = per le definizioni e ≡ per le asserzioni.
-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- una definizione simile si dice BEN FONDATA

{-
Con _ si indica il dummy name che può essere riusato ovunque e sempre. Altri nomi vanno usati solo una volta in un modulo. La prima riga definisce un tipo (2 + 3 ≡ 5) e il termine dà un evidenza. 

L'evidenza che un valore è uguale a se stesso è scritto `refl`. Inoltre è dovere dell'autore scrivere le equazioni in senso logico per il elttore.
tipo    <-> proposizione
termine <-> evidenza
proof == evidence
-}

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

-- ESPONENZIALE (grazie alla moltiplicazione)

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

{-
Con infix <n> ... dichiariamo la precedenza dell'operatore
infixl -> associativo a sinistra
infixr -> associativo a destra
infix  -> servono sempre le parentesi per disambiguare
-}

infixl 6  _+_  _∸_
-- infixl 7  _*_


-- Tutto ciò che sappiamo sui naturali è definito in Data.Nat (modulo)