# Appunti AGDA

Per dichiarare un **modulo** scriviamo
```agda
module MyModule where
```
dove `MyModule` è il nome del modulo.

# 

Queste sono **regole di inferenza**, composta di eventuali ipotesi e conclusione.
```agda
{-
  --------
  zero : ℕ  

  m : ℕ
  ---------
  suc m : ℕ 
-}
```

# 

- ℕ è un **datatype**
- zero e suc sono **costruttori**
- Set è un tipo di dato
- con data si dà una def. induttiva

```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ
```

# 

Un **pragma** è un tipo speciale di commento, qui ci permette di scrivere i numeri naturali normalmente.
```agda
{-# BUILTIN NATURAL ℕ #-}
```

# 

Con `import` posso importare altri moduli (es. stdlib) e con `as` gli assegno un alias.
Tutto ciò compreso dopo `using` in (...) viene importato nello scope
```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
```

# 

Possiamo specificare come usare gli operatori:
- \_x\_ operatore infisso
- _x  operatore postfisso
- x_  operatore prefisso

Usiamo `=` per le def. e `≡` per le asserzioni.
Con `_` indichiamo il "dummy name" una variabile usabile sempre ed ovunque. 
L'autore ha il dovere di scrivere le equazioni in senso logico per il lettore.

# 

Esempio di definizione:

```agda
-- addizione
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)
```

Esempio di **proposizione** e **dimostrazione**:
```agda
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
```

# 

Tutto ciò che sappiamo naturali è definito in `Data.Nat`.

`∸` = monus, operatore di sottrazione naturale 

Per quanto riguarda la precedenza degli operatori:
- `infixl` = associatività a sinistra
- `infixr` = associatività a destra
- `infix`  = associatività da chiarire con parentesi (disambiguare)

```agda
infixl 6  _+_  _∸_
infixl 7  _*_
```