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

module Arithmetic' where

  _+_ _×_ : ℕ → ℕ → ℕ

  x + y = h y
   where
   h : ℕ → ℕ
   h = ℕ-iteration ℕ x succ

  x × y = h y
   where
     h : ℕ → ℕ
     h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_

module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ +
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

  infix 10 _≤_
  infix 10 _≥_

-- The binary sum type constructor +

data _+_ {𝓤 𝓥} (X : 𝓤 +) (Y : 𝓥 +) : 𝓤 ⊔ 𝓥 + where
  inl : X → X + Y
  inr : Y → X + Y

+-induction : {X : 𝓤 +} {Y : 𝓥 +} (A : X + Y → 𝓦 +)
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y)  → A z

+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 +} {Y : 𝓥 +} {A : 𝓦 +}
            → (X → A)
            → (Y → A)
            → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)

𝟚 : 𝓤₀ +
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

-- show some property for 0, and 1 and get it for 𝟚
𝟚-induction : (A : 𝟚 → 𝓤 +) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

-- ∑ types !!

record ∑ {𝓤 𝓥} {X : 𝓤 +} (Y : X → 𝓥 +) : 𝓤 ⊔ 𝓥 + where
  constructor _,_
  field
    x : X
    y : Y x

pr₁ : {X : 𝓤 +} {Y : X → 𝓥 +} → ∑ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 +} {Y : X → 𝓥 +} → (z : ∑ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-- a version of ∑ with the X type explicit
-∑ : {𝓤 𝓥 : Universe} (X : 𝓤 +) (Y : X → 𝓥 +) → 𝓤 ⊔ 𝓥 +
-∑ X Y = ∑ Y

syntax -∑ X (λ x → y) = ∑ x ∶ X , y

∑-induction : {X : 𝓤 +} {Y : X → 𝓥 +} {A : ∑ Y → 𝓦 +}
            → ((x : X) (y : Y x) → A (x , y))
            → ((x , y) : ∑ Y) → A (x , y)

∑-induction g (x , y) = g x y

-- apparently the inverse of induction is "curry"

curry : {X : 𝓤 +} {Y : X → 𝓥 +} {A : ∑ Y → 𝓦 +}
      → (((x , y) : ∑ Y) → A (x , y))
      → ((x : X) (y : Y x) → A (x , y))

curry f x y = f (x , y)

_×_ : 𝓤 + → 𝓥 + → 𝓤 ⊔ 𝓥 +
X × Y = ∑ x ∶ X , Y

Π : {X : 𝓤 +} (A : X → 𝓥 +) → 𝓤 ⊔ 𝓥 +
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 +) (Y : X → 𝓥 +) → 𝓤 ⊔ 𝓥 +
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ∶ A , b

id : {X : 𝓤 +} → X → X
id x = x

id_exp : (X : 𝓤 +) → X → X
id_exp X x = x

_∘_ : {X : 𝓤 +} {Y : 𝓥 +} {Z : Y → 𝓦 +}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)

g ∘ f = λ x → g (f x)

domain : {X : 𝓤 +} {Y : 𝓥 +} → (X → Y) → 𝓤 +
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 +} {Y : 𝓥 +} → (X → Y) → 𝓥 +
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 +} → X → 𝓤 +
type-of {𝓤} {X} x = X

-- finally we get to identity

data Id' {𝓤} (X : 𝓤 +) (x : X) : 𝓤 + where
  refl' : Id' X x

data Id {𝓤} (X : 𝓤 +) : X → X → 𝓤 + where
  refl : (x : X) → Id X x x

_≡_ : {X : 𝓤 +} → X → X → 𝓤 +
x ≡ y = Id _ x y

𝕁 : (X : 𝓤 +) (A : (x y : X) → x ≡ y → 𝓥 +)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y)
  → A x y p

𝕁 X A f x x (refl x) = f x

-- I guess this is like "based path induction"?
ℍ : {X : 𝓤 +} (x : X) (B : (y : X) → x ≡ y → 𝓥 +)
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p

ℍ x B b x (refl x) = b

-- Basic constructions with the identity type

transport : {X : 𝓤 +} (A : X → 𝓥 +) {x y : X}
          → x ≡ y → (A x → A y)

transport A (refl x) = id_exp (A x)

-- define transport with 𝕁
transport𝕁 : {X : 𝓤 +} (A : X → 𝓥 +) {x y : X}
           → x ≡ y → A x → A y

transport𝕁 {𝓤} {𝓥} {X} A {x} {y} =
  𝕁 X (λ x y p → A x → A y) (λ x → id_exp (A x)) x y

nondep-ℍ : {X : 𝓤 +} (x : X) (A : X → 𝓥 +)
         → A x → (y : X) → x ≡ y → A y

nondep-ℍ x A = ℍ x (λ y _ → A y)

transportℍ : {X : 𝓤 +} (A : X → 𝓥 +) {x y : X}
           → x ≡ y → A x → A y

transportℍ A {x} {y} p a = nondep-ℍ x A a y p

transports-agreement : {X : 𝓤 +} (A : X → 𝓥 +) {x y : X} (p : x ≡ y)
                     → (transportℍ A p ≡ transport A p)
                     × (transport𝕁 A p ≡ transport A p)

transports-agreement A (refl x) = refl (transport A (refl x))
                                  , refl (transport A (refl x))

lhs : {X : 𝓤 +} {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 +} {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y

_∙_ : {X : 𝓤 +} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p

-- some equational notation
_≡⟨_⟩_ : {X : 𝓤 +} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 +} (x : X) → x ≡ x
x ∎ = refl x

_⁻¹ : {X : 𝓤 +} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))


ap : {X : 𝓤 +} {Y : 𝓥 +} (f : X → Y) {x x' : X}
   → x ≡ x' → f x ≡ f x'

ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))

-- pointwise equality of functions
_∼_ : {X : 𝓤 +} {A : X → 𝓥 +} → Π A → Π A → 𝓤 ⊔ 𝓥 +
f ∼ g = ∀ x → f x ≡ g x

¬¬ ¬¬¬ : 𝓤 + → 𝓤 +
¬¬ A = ¬(¬ A)
¬¬¬ A = ¬ (¬¬ A)

dni : (A : 𝓤 +) → A → ¬¬ A
dni A a u = u a

contrapositive : {A : 𝓤 +} {B : 𝓥 +} → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)

tno : (A : 𝓤 +) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

_⇔_ : 𝓤 + → 𝓥 + → 𝓤 ⊔ 𝓥 +
X ⇔ Y = (X → Y) × (Y → X)

lr-implication : {X : 𝓤 +} {Y : 𝓥 +} → (X ⇔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 +} {Y : 𝓥 +} → (X ⇔ Y) → (Y → X)
rl-implication = pr₂

absurdity³-is-absurdity : {A : 𝓤 +} → ¬¬¬ A ⇔ ¬ A
absurdity³-is-absurdity {U} {A} = firstly , secondly
  where
    firstly : ¬¬¬ A → ¬ A
    firstly = contrapositive (dni A)

    secondly : ¬ A → ¬¬¬ A
    secondly = dni (¬ A)

_≇_ : {X : 𝓤 +} → X → X → 𝓤 +
x ≇ y = ¬(x ≡ y)

≇-sym : {X : 𝓤 +} {x y : X} → x ≇ y → y ≇ x
≇-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)

-- this proof works because we can transport the universe Id function
-- across identities
Id→Fun : {X Y : 𝓤 +} → X ≡ Y → X → Y
Id→Fun {𝓤} = transport (id_exp (𝓤 +))

𝟙-is-not-𝟘 : 𝟙 ≇ 𝟘
𝟙-is-not-𝟘 p = (Id→Fun p) ⋆

₁-is-not-₀ : ₁ ≇ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
  where
    f : 𝟚 → 𝓤₀ +
    f ₀ = 𝟘
    f ₁ = 𝟙

    q : 𝟙 ≡ 𝟘
    q = ap f p

decidable : 𝓤 + → 𝓤 +
decidable A = A + ¬ A

has-decidable-eq : 𝓤 + → 𝓤 +
has-decidable-eq A = ∀ (x y : A) → decidable (x ≡ y)

𝟚-has-decidable-eq : has-decidable-eq 𝟚
𝟚-has-decidable-eq ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-eq ₀ ₁ = inr (≇-sym ₁-is-not-₀)
𝟚-has-decidable-eq ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-eq ₁ ₁ = inl (refl ₁)

not-zero-is-one : (n : 𝟚) → n ≇ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁

-- finally on to univalence!

is-singleton : 𝓤 + → 𝓤 +
is-singleton X = ∑ c ∶ X , ((x : X) → c ≡ x)

-- the element c is known as the center of contraction

is-center : (X : 𝓤 +) → X → 𝓤 +
is-center X c = (x : X) → c ≡ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl ⋆)

center : (X : 𝓤 +) → is-singleton X → X
center X (c , ϕ) = c

centrality : (X : 𝓤 +) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , ϕ) = ϕ

is-subsingleton : 𝓤 + → 𝓤 +
is-subsingleton X = (x y : X) → x ≡ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ≡ y) x

singletons-are-subsingletons : (X : 𝓤 +) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , ϕ) x y =
                             x ≡⟨ (ϕ x)⁻¹ ⟩
                             c ≡⟨ ϕ y     ⟩
                             y ∎

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton = singletons-are-subsingletons 𝟙 𝟙-is-singleton

pointed-subsingletons-are-singletons : (X : 𝓤 +) → X
                                     → is-subsingleton X → is-singleton X

pointed-subsingletons-are-singletons X x s = (x , s x)

-- Sets (or 0-groupoids)
is-set : 𝓤 + → 𝓤 +
is-set X = (x y : X) → is-subsingleton (x ≡ y)

EM EM' : ∀ 𝓤 → 𝓤 ⁺ +
EM 𝓤 = (X : 𝓤 +) → is-subsingleton X → X + ¬ X
EM' 𝓤 = (X : 𝓤 +) → is-subsingleton X → is-singleton X + is-empty X

EM-gives-EM' : EM 𝓤 → EM' 𝓤
EM-gives-EM' em X s = γ (em X s)
  where
    γ : X + ¬ X → is-singleton X + is-empty X
    γ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
    γ (inr x) = inr x

EM'-gives-EM : EM' 𝓤 → EM 𝓤
EM'-gives-EM em' X s = γ (em' X s)
  where
    γ : is-singleton X + is-empty X → X + ¬ X
    γ (inl i) = inl (center X i)
    γ (inr x) = inr x

no-unicorns : ¬(∑ X ∶ 𝓤 + , is-subsingleton X × ¬(is-singleton X) × ¬(is-empty X))
no-unicorns (X , i , f , g) = c
  where
    e : is-empty X
    e x = f (pointed-subsingletons-are-singletons X x i)

    c : 𝟘
    c = g e

module magmas where

  Magma : (𝓤 : Universe) → 𝓤 ⁺ +
  Magma 𝓤 = ∑ X ∶ 𝓤 + , is-set X × (X → X → X)

  -- this denotes the underlying set of the Magma
  -- X is the set, i is the proofs that X is a set, and _∙_ is the set operator
  ⟨_⟩ : Magma 𝓤 → 𝓤 +
  ⟨ X , i , _∙_ ⟩ = X

  -- this is basically a tuple projection
  magma-is-set : (M : Magma 𝓤) → is-set ⟨ M ⟩
  magma-is-set (X , i , _∙_) = i

  magma-operation : (M : Magma 𝓤) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
  magma-operation (X , i , _∙_) = _∙_

  syntax magma-operation M x y = x ∙⟨ M ⟩ y

  -- functions on sets are called a homomorphism when it commutes with the magma op
  is-magma-hom : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 +
  is-magma-hom M N f = (x y : ⟨ M ⟩) → f (x ∙⟨ M ⟩ y ) ≡ f x ∙⟨ N ⟩ f y

  id-is-magma-hom : (M : Magma 𝓤) → is-magma-hom M M (id_exp ⟨ M ⟩)
  id-is-magma-hom M = λ (x y : ⟨ M ⟩) → refl (x ∙⟨ M ⟩ y)

  -- a magma iso-morphism is f is a homomorphism from M -> N
  -- and there exists a g that is a homomorphism from N -> M
  -- such that g ∘ f is id on M, and f ∘ g is id on N
  is-magma-iso : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 +
  is-magma-iso M N f = is-magma-hom M N f
                     × (∑ g ∶ (⟨ N ⟩ → ⟨ M ⟩), is-magma-hom N M g
                                               × (g ∘ f ∼ id_exp ⟨ M ⟩)
                                               × (f ∘ g ∼ id_exp ⟨ N ⟩))

  id-is-magma-iso : (M : Magma 𝓤) → is-magma-iso M M (id_exp ⟨ M ⟩)
  id-is-magma-iso M = id-is-magma-hom M ,
                      id_exp ⟨ M ⟩ ,
                      id-is-magma-hom M ,
                      refl ,
                      refl

  -- any identifications of magmas, gives us a magma isomorphism for "free"
  Id→iso : {M N : Magma 𝓤} → M ≡ N → ⟨ M ⟩ → ⟨ N ⟩
  Id→iso p = transport ⟨_⟩ p

  Id→iso-is-iso : {M N : Magma 𝓤} (p : M ≡ N) → is-magma-iso M N (Id→iso p)
  Id→iso-is-iso (refl M) = id-is-magma-iso M

  -- this is just an excercise proof to try using J directly instead of using
  -- pattern matching directly
  Id→iso-is-iso' : (M N : Magma 𝓤) (p : M ≡ N) → is-magma-iso M N (Id→iso p)
  Id→iso-is-iso' {𝓤} = 𝕁 (Magma 𝓤) A id-is-magma-iso
    where
      A : _
      A = λ (M N : Magma 𝓤) (p : M ≡ N) → is-magma-iso M N (Id→iso p)

  _≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 +
  M ≅ₘ N = ∑ f ∶ (⟨ M ⟩ → ⟨ N ⟩), is-magma-iso M N f

  magma-Id→iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
  magma-Id→iso p = (Id→iso p , Id→iso-is-iso p)

  -- if we drop the requirement that X be a set, then we get
  -- an infinite family of magmas
  ∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ +
  ∞-Magma 𝓤 = ∑ X ∶ 𝓤 + , (X → X → X)

module monoids where

  left-neutral : {X : 𝓤 +} → X → (X → X → X) → 𝓤 +
  left-neutral e _∙_ = ∀ x → e ∙ x ≡ x 

  right-neutral : {X : 𝓤 +} → X → (X → X → X) → 𝓤 +
  right-neutral e _∙_ = ∀ x → x ∙ e ≡ x 

  associative : {X : 𝓤 +} → (X → X → X) → 𝓤 +
  associative _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  -- a monoid is a set with an element that is a left and right neutral element
  -- along with an operator that is associative
  Monoid : (𝓤 : Universe) → 𝓤 ⁺ +
  Monoid 𝓤 = ∑ X ∶ 𝓤 + , is-set X
                       × (∑ ∙ ∶ (X → X → X) , (∑ e ∶ X , (left-neutral e ∙)
                                                       × (right-neutral e ∙)
                                                       × (associative ∙)))

-- The identity type in univalent mathematics!!

-- we can view type X as a category, with hom-types rather than hom-sets

refl-left : {X : 𝓤 +} {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝓤 +} {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p

∙-assoc : {X : 𝓤 +} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
        → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)

∙-assoc p q (refl z) = refl (p ∙ q)

inv-left∙ : {X : 𝓤 +} {x y : X} (p : x ≡ y)
          → p ⁻¹ ∙ p ≡ refl y

inv-left∙ (refl x) = refl (refl x)

inv-right∙ : {X : 𝓤 +} {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x

inv-right∙ (refl x) = refl (refl x)

-- some more boring properties
⁻¹-involutive : {X : 𝓤 +} {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p

⁻¹-involutive (refl x) = refl (refl x)

ap-refl : {X : 𝓤 +} {Y : 𝓥 +} (f : X → X) (x : X)
        → ap f (refl x) ≡ refl (f x)

ap-refl f x = refl (refl (f x))

ap-∙ : {X : 𝓤 +} {Y : 𝓥 +} (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)

ap⁻¹ : {X : 𝓤 +} {Y : 𝓥 +} (f : X → Y) {x y : X} (p : x ≡ y)
     → (ap f p)⁻¹ ≡ ap f (p ⁻¹)

ap⁻¹ f (refl x) = refl (refl (f x))

ap-id : {X : 𝓤 +} {x y : X} (p : x ≡ y)
      → ap id p ≡ p

ap-id (refl x) = refl (refl x)

ap-∘ : {X : 𝓤 +} {Y : 𝓥 +} {Z : 𝓦 +}
       (f : X → Y) (g : Y → Z) {x y : X} (p : x ≡ y)
     → ap (g ∘ f) p ≡ (ap g ∘ ap f) p

ap-∘ f g (refl x) = refl (refl ((g (f x))))

transport∙ : {X : 𝓤 +} (A : X → 𝓥 +) {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → transport A (p ∙ q) ≡ transport A q ∘ transport A p

transport∙ A (refl x) (refl y) = refl id

-- the morphisms of ∞-presheaves are natural transformations
Nat : {X : 𝓤 +} → (X → 𝓥 +) → (X → 𝓦 +) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 +
Nat A B = (x : domain A) → A x → B x

-- Nats commute in the way that you expect
Nats-are-natural : {X : 𝓤 +} (A : X → 𝓥 +) (B : X → 𝓦 +) (τ : Nat A B)
                 → {x y : X} (p : x ≡ y)
                 → τ y ∘ transport A p ≡ transport B p ∘ τ x

Nats-are-natural A B τ (refl x) = refl (τ x)

Nat∑ : {X : 𝓤 +} {A : X → 𝓥 +} {B : X → 𝓦 +} → Nat A B → ∑ A → ∑ B
Nat∑ τ (x , a) = (x , τ x a)

transport-ap : {X : 𝓤 +} {Y : 𝓥 +} (A : Y → 𝓦 +)
               (f : X → Y) {x x' : X} (p : x ≡ x') (a : A (f x))
             → transport (A ∘ f) p a ≡ transport A (ap f p) a

transport-ap A f (refl x) a = refl a

apd : {X : 𝓤 +} {A : X → 𝓥 +} (f : (x : X) → A x) {x y : X}
      (p : x ≡ y) → transport A p (f x) ≡ f y

apd f (refl x) = refl (f x)

to-∑-≡ : {X : 𝓤 +} {A : X → 𝓥 +} {(x , a) (y , b) : ∑ A}
       → (∑ p ∶ x ≡ y , transport A p a ≡ b)
       → (x , a) ≡ (y , b)

to-∑-≡ (refl x , refl a) = refl (x , a)

from-∑-≡ : {X : 𝓤 +} {A : X → 𝓥 +} {(x , a) (y , b) : ∑ A}
         → (x , a) ≡ (y , b)
         → ∑ p ∶ x ≡ y , transport A p a ≡ b

from-∑-≡ (refl (x , a)) = (refl x , refl a)

to-∑-≡' : {X : 𝓤 +} {A : X → 𝓥 +} {x : X} {a a' : A x}
        → a ≡ a' → Id (∑ A) (x , a) (x , a')

to-∑-≡' {𝓤} {𝓥} {X} {A} {x} = ap (λ - → (x , -))

transport-× : {X : 𝓤 +} (A : X → 𝓥 +) (B : X → 𝓦 +)
              {x y : X} (p : x ≡ y) {(a , b) : A x × B x}
            → transport (λ x → A x × B x) p (a , b)
            ≡ (transport A p a , transport B p b)

transport-× A B (refl _) = refl _

transportd : {X : 𝓤 +} (A : X → 𝓥 +) (B : (x : X) → A x → 𝓦 +)
             {x : X} ((a , b) : ∑ a ∶ A x , B x a) {y : X} (p : x ≡ y)
           → B x a → B y (transport A p a)

transportd A B (a , b) (refl x) = id

transport-∑ : {X : 𝓤 +} (A : X → 𝓥 +) (B : (x : X) → A x → 𝓦 +)
              {x : X} {y : X} (p : x ≡ y) {(a , b) : ∑ a ∶ A x , B x a}
            → transport (λ - → ∑ (B -)) p (a , b)
            ≡ transport A p a , transportd A B (a , b) p b

transport-∑ A B (refl x) {a , b} = refl (a , b)

-- Voevodsky's notion of h-level

_is-of-hlevel_ : 𝓤 + → ℕ → 𝓤 +
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)

-- Hedberg's Theorem

-- w here stands for wildly
wconstant : {X : 𝓤 +} {Y : 𝓥 +} → (X → Y) → 𝓤 ⊔ 𝓥 +
wconstant f = (x x' : domain f) → f x ≡ f x'

wconstant-endomap : 𝓤 + → 𝓤 +
wconstant-endomap X = ∑ f ∶ (X → X), wconstant f

wcmap : (X : 𝓤 +) → wconstant-endomap X → (X → X)
wcmap X (f , w) = f

wcmap-constancy : (X : 𝓤 +) (c : wconstant-endomap X)
                → wconstant (wcmap X c)
wcmap-constancy X (f , w) = w

-- A type is a set iff it's identity types all have designated wconstant endomaps

Hedberg : {X : 𝓤 +} (x : X)
        → ((y : X) → wconstant-endomap (x ≡ y))
        → (y : X) → is-subsingleton (x ≡ y)

Hedberg {𝓤} {X} x c y p q =
  p                        ≡⟨ a y p ⟩
  (f x (refl x))⁻¹ ∙ f y p ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
  (f x (refl x))⁻¹ ∙ f y q ≡⟨ (a y q)⁻¹ ⟩
  q                        ∎

  where
    f : (y : X) → x ≡ y → x ≡ y
    f y = wcmap (x ≡ y) (c y)

    κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
    κ y = wcmap-constancy (x ≡ y) (c y)

    a : (y : X) (p : x ≡ y) → p ≡ (f x (refl x))⁻¹ ∙ f y p
    a x (refl x) = (inv-left∙ (f x (refl x)))⁻¹

wconstant-≡-endomaps : 𝓤 + → 𝓤 +
wconstant-≡-endomaps X = (x y : X) → wconstant-endomap (x ≡ y)

sets-have-wconstant-≡-endomaps : (X : 𝓤 +) → is-set X → wconstant-≡-endomaps X
sets-have-wconstant-≡-endomaps X s x y = (f , κ)
  where
    f : x ≡ y → x ≡ y
    f p = p

    κ : (p q : x ≡ y) → f p ≡ f q
    κ p q = s x y p q

types-with-wconstant-≡-endomaps-are-sets : (X : 𝓤 +)
                                         → wconstant-≡-endomaps X → is-set X

types-with-wconstant-≡-endomaps-are-sets X c x =
  Hedberg x (λ y → wcmap (x ≡ y) (c x y) , wcmap-constancy (x ≡ y) (c x y))

subsingletons-have-wconstant-≡-endomaps : (X : 𝓤 +)
                                        → is-subsingleton X
                                        → wconstant-≡-endomaps X

subsingletons-have-wconstant-≡-endomaps X s x y = (f , κ)
  where
    f : x ≡ y → x ≡ y
    f p = s x y

    κ : (p q : x ≡ y) → f p ≡ f q
    κ p q = refl (s x y)

subsingletons-are-sets : (X : 𝓤 +) → is-subsingleton X → is-set X
subsingletons-are-sets X s = types-with-wconstant-≡-endomaps-are-sets X
                             (subsingletons-have-wconstant-≡-endomaps X s)

singletons-are-sets : (X : 𝓤 +) → is-singleton X → is-set X
singletons-are-sets X = subsingletons-are-sets X ∘ singletons-are-subsingletons X

𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingletons-are-sets 𝟘 𝟘-is-subsingleton

𝟙-is-set : is-set 𝟙
𝟙-is-set = subsingletons-are-sets 𝟙 𝟙-is-subsingleton

subsingletons-are-of-hlevel-1 : (X : 𝓤 +)
                              → is-subsingleton X
                              → X is-of-hlevel 1

subsingletons-are-of-hlevel-1 X = g
  where
    g : ((x y : X) → x ≡ y) → (x y : X) → is-singleton (x ≡ y)
    g t x y = t x y , subsingletons-are-sets X t x y (t x y)

types-of-hlevel-1-are-subsingletons : (X : 𝓤 +)
                                    → X is-of-hlevel 1
                                    → is-subsingleton X

types-of-hlevel-1-are-subsingletons X = f
  where
    f : ((x y : X) → is-singleton (x ≡ y)) → (x y : X) → x ≡ y
    f s x y = center (x ≡ y) (s x y)

sets-are-of-hlevel-2 : (X : 𝓤 +) → is-set X → X is-of-hlevel 2
sets-are-of-hlevel-2 X = g
  where
    g : ((x y : X) → is-subsingleton (x ≡ y)) → (x y : X) → (x ≡ y) is-of-hlevel 1
    g t x y = subsingletons-are-of-hlevel-1 (x ≡ y) (t x y)

types-of-hlevel-2-are-sets : (X : 𝓤 +) → X is-of-hlevel 2 → is-set X
types-of-hlevel-2-are-sets X = f
  where
    f : ((x y : X) → (x ≡ y) is-of-hlevel 1) → (x y : X) → is-subsingleton (x ≡ y)
    f s x y = types-of-hlevel-1-are-subsingletons (x ≡ y) (s x y)

hlevel-upper-closed : (X : 𝓤 +) (n : ℕ) → X is-of-hlevel n → X is-of-hlevel (succ n)
hlevel-upper-closed X zero = γ
  where
    γ : is-singleton X → (x y : X) → is-singleton (x ≡ y)
    γ h x y = p , subsingletons-are-sets X k x y p
      where
        k : is-subsingleton X
        k = singletons-are-subsingletons X h

        p : x ≡ y
        p = k x y

hlevel-upper-closed X (succ n) = λ h x y → hlevel-upper-closed (x ≡ y) n (h x y)

-- retracts

has-section : {X : 𝓤 +} {Y : 𝓥 +} → (X → Y) → 𝓤 ⊔ 𝓥 +
has-section r = ∑ s ∶ (codomain r → domain r), r ∘ s ∼ id

_◁_ : 𝓤 + → 𝓥 + → 𝓤 ⊔ 𝓥 +
X ◁ Y = ∑ r ∶ (Y → X), has-section r

retraction : {X : 𝓤 +} {Y : 𝓥 +} → X ◁ Y → (Y → X)
retraction (r , s , η) = r

section : {X : 𝓤 +} {Y : 𝓥 +} → X ◁ Y → (X → Y)
section (r , s , η) = s

retract-equation : {X : 𝓤 +} {Y : 𝓥 +} → (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ∼ id_exp X

retract-equation (r , s , η) = η

retraction-has-section : {X : 𝓤 +} {Y : 𝓥 +} (ρ : X ◁ Y)
                       → has-section (retraction ρ)

retraction-has-section (r , h) = h

id-◁ : (X : 𝓤 +) → X ◁ X
id-◁ X = id_exp X , id_exp X , refl

pred : ℕ → ℕ
pred 0        = 0
pred (succ n) = n

pred-◁ : ℕ ◁ ℕ
pred-◁ = pred , succ , refl

_◁∘_ : {X : 𝓤 +} {Y : 𝓥 +} {Z : 𝓦 +} → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
  where
    η'' = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
                r (s x)           ≡⟨ η x ⟩
                x                 ∎

_◁⟨_⟩_ : (X : 𝓤 +) {Y : 𝓥 +} {Z : 𝓦 +} → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ

_◀ : (X : 𝓤 +) → X ◁ X
X ◀ = id-◁ X

∑-retract : {X : 𝓤 +} {A : X → 𝓥 +} {B : X → 𝓦 +}
          → ((x : X) → A x ◁ B x) → ∑ A ◁ ∑ B

∑-retract {𝓤} {𝓥} {𝓦} {X} {A} {B} ρ = Nat∑ r , Nat∑ s , η'
  where
    r : (x : X) → B x → A x
    r x = retraction (ρ x)

    s : (x : X) → A x → B x
    s x = section (ρ x)

    η : (x : X) (a : A x) → r x (s x a) ≡ a
    η x = retract-equation (ρ x)

    η' : (σ : ∑ A) → Nat∑ r (Nat∑ s σ) ≡ σ
    η' (x , a) = x , r x (s x a) ≡⟨ to-∑-≡' (η x a) ⟩
                 x , a           ∎


infixr 30 _∙_
infixr 30 _×_
infixr 50 _,_
infixr -1 -∑
infixr  0 _≡⟨_⟩_
infix   1 _∎
infix   0 _≡_
infixl 70 _∘_
infix   0 _∼_
infix  40 _⁻¹
