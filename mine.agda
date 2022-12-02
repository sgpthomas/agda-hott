{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module mine where

open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

-- The one type (representing truth values)

data 𝟙 : 𝓤₀ +  where
 ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 +) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 +) → B → 𝟙 → B
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙 : {X : 𝓤 +} → X → 𝟙
!𝟙 x = ⋆

-- The empty type (0)

data 𝟘 : 𝓤₀ + where

𝟘-induction : (A : 𝟘 → 𝓤 +) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 +) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 +) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 + → 𝓤 +
is-empty X = X → 𝟘

¬ : 𝓤 + → 𝓤 +
¬ X = X → 𝟘


-- The type ℕ of natural numbers

data ℕ : 𝓤₀ + where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 +)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
  where
   h : (n : ℕ) → A n
   h 0         = a₀
   h (succ n)  = f n (h n)

-- we get recursion by passing in a constant type family into the inductor
ℕ-recursion : (X : 𝓤 +)
            → X
            → (ℕ → X → X)
            → (ℕ → X)
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 +)
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

-- quick diversion into arithmetic
module Arithmetic where

  _+_ _×_ : ℕ → ℕ → ℕ

  x + 0       = x
  x + succ y  = succ (x + y)

  x × 0       = 0
  x × succ y  = x + (x × y)

  infixl 20 _+_
  infixl 21 _×_

