module AgdaSort where

--------------------------------------------------------------------------------
-- Lists

infixr 5 _∷_
data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

foldr : ∀ {A} {B : Set} → (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (a ∷ as) = f a (foldr f b as)

--------------------------------------------------------------------------------
-- Trivial type, and empty type

record True : Set where constructor tt
data False : Set where

infix 3 ¬_
¬_ : Set → Set
¬ X = X → False

absurd : {X : Set} → False → X
absurd ()

--------------------------------------------------------------------------------
-- Dependent product and sum

infixr 4 _,_

record Prod (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 2 _∧_
_∧_ : (A B : Set) → Set
A ∧ B = Prod A (λ _ → B)

data Either (A : Set) (B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

[_,_] : ∀ {A B} {C : Set} → (A → C) → (B → C) → Either A B → C
[ f , g ] (left x)  = f x
[ f , g ] (right x) = g x

--------------------------------------------------------------------------------
-- Relations

Rel : Set → Set₁
Rel X = X → X → Set

Decidable : ∀ {X} → Rel X → Set
Decidable _≤_ = ∀ x y → Either (x ≤ y) (¬ (x ≤ y))

record Equivalence {X : Set} (_≈_ : Rel X) : Set₁ where
  field
    refl  : ∀ {x}     → x ≈ x
    sym   : ∀ {x y}   → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

record TotalOrder {X : Set} (_≈_ : Rel X) (_≤_ : Rel X) : Set₁ where
  field
    antisym     : ∀ {x y}   → x ≤ y → y ≤ x → x ≈ y
    trans       : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    total       : ∀ x y     → Either (x ≤ y) (y ≤ x)
    reflexive   : ∀ {x y}   → x ≈ y → x ≤ y
    equivalence : Equivalence _≈_

--------------------------------------------------------------------------------
-- Sorting

module Sort {X : Set} {_≈_ _≤_ : Rel X}
            (_≈?_ : Decidable _≈_) (_≤?_ : Decidable _≤_)
            (ord : TotalOrder _≈_ _≤_) where
  open TotalOrder ord using (trans; total; reflexive; equivalence)
  open Equivalence equivalence using (refl)

  -- Insertion sort

  data ⊥X⊤ : Set where
    ⊤ ⊥ : ⊥X⊤
    ⟦_⟧ : X → ⊥X⊤

  _≤̂_ : ⊥X⊤ → ⊥X⊤ → Set
  ⊥     ≤̂ _     = True
  ⟦ n ⟧ ≤̂ ⟦ m ⟧ = n ≤ m
  _     ≤̂ ⊤     = True
  _     ≤̂ _     = False

  -- Brilliant.
  ≤̂-trans : ∀ l x u → l ≤̂ ⟦ x ⟧ → ⟦ x ⟧ ≤̂ u → l ≤̂ u
  ≤̂-trans ⊤     _ ⊤     _   _   = _
  ≤̂-trans ⊤     _ ⊥     _   ()
  ≤̂-trans ⊤     _ ⟦ _ ⟧ ()  _  
  ≤̂-trans ⊥     _ _     _   _   = _
  ≤̂-trans ⟦ _ ⟧ _ ⊤     _   _   = _
  ≤̂-trans ⟦ _ ⟧ _ ⊥     _   ()
  ≤̂-trans ⟦ l ⟧ x ⟦ u ⟧ l≤x x≤u = trans l≤x x≤u

  _≤_≤_ : ⊥X⊤ → X → ⊥X⊤ → Set
  l ≤ x ≤ u = l ≤̂ ⟦ x ⟧ ∧ ⟦ x ⟧ ≤̂ u

  data OList (l u : ⊥X⊤) : Set where
    nil  : l ≤̂ u → OList l u
    cons : ∀ x (xs : OList ⟦ x ⟧ u) → l ≤ x ≤ u → OList l u

  toList : ∀ {l u} → OList l u → List X
  toList (nil _) = []
  toList (cons x xs _) = x ∷ toList xs

  insert : ∀ {l u} → (x : X) (xs : OList l u) {l≤x≤u : l ≤ x ≤ u} →
           OList l u
  insert y (nil _) {l≤y , y≤u} = cons y (nil y≤u) (l≤y , y≤u)
  insert y (cons x xs (l≤x , x≤u)) with y ≤? x
  insert y (cons x xs (l≤x , x≤u)) {l≤y , y≤u} | left  y≤x =
    cons y (cons x xs (y≤x , x≤u)) (l≤y , y≤u)
  insert y (cons x xs (l≤x , x≤u)) {l≤y , y≤u} | right y>x =
    cons x (insert x xs {reflexive refl , x≤u}) (l≤x , x≤u)

  isort′ : List X → OList ⊥ ⊤
  isort′ = foldr (λ x xs → insert x xs) (nil _)

  isort : List X → List X
  isort xs = toList (isort′ xs)

  -- Tree sort

  data Tree (l u : ⊥X⊤) : Set where
    leaf : l ≤̂ u → Tree l u
    node : (x : X) → Tree l ⟦ x ⟧ → Tree ⟦ x ⟧ u → Tree l u

  newLeaf : ∀ {l u} → (x : X) → Tree l u → {l≤x≤u : l ≤ x ≤ u} → Tree l u
  newLeaf x (leaf _) {l≤x , x≤u} = node x (leaf l≤x) (leaf x≤u)
  newLeaf x (node y ly yu) with x ≤? y
  newLeaf x (node y ly yu) {l≤x , x≤u} | left x≤y =
    node y (newLeaf x ly {l≤x , x≤y}) yu
  newLeaf {l} {u} x (node y ly yu) {l≤x , x≤u} | right x>y  =
    node y ly
         (newLeaf x yu {[ (λ p → absurd (x>y p)) , (λ p → p) ] (total x y) , x≤u})

  fromList : List X → Tree ⊥ ⊤
  fromList = foldr (λ x xs → newLeaf x xs) (leaf _)

  OList-≤ : ∀ {l u} → OList l u → l ≤̂ u
  OList-≤ (nil l≤u) = l≤u
  OList-≤ {l} {u} (cons x xu (l≤x , x≤u)) = ≤̂-trans l x u l≤x (OList-≤ xu)

  _⇒_++_ : ∀ {l u} → (x : X) → OList l ⟦ x ⟧ → OList ⟦ x ⟧ u →
           OList l u
  x ⇒ (nil l≤u) ++ xu = cons x xu (l≤u , OList-≤ xu)
  _⇒_++_ {u = u} x (cons y yx (l≤y , y≤x)) xu =
    cons y (x ⇒ yx ++ xu) (l≤y , ≤̂-trans ⟦ y ⟧ x u y≤x (OList-≤ xu))

  flatten : ∀ {l u} → Tree l u → OList l u
  flatten (leaf l≤u) = (nil l≤u)
  flatten (node x lx xu) =  x ⇒ flatten lx ++ flatten xu

  treeSort′ : List X → OList ⊥ ⊤
  treeSort′ xs = flatten (foldr (λ x xs → newLeaf x xs) (leaf _) xs)

  treeSort : List X → List X
  treeSort xs = toList (treeSort′ xs)

--------------------------------------------------------------------------------
-- Propositional equality

module PropositionalEquality where
  data _≡_ {X : Set} : Rel X where
    refl : ∀ {x} → x ≡ x

  sym : ∀ {X} {x y : X} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {X} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  cong : ∀ {X} {x y : X} → (f : X → X) → x ≡ y → f x ≡ f y
  cong _ refl = refl

  equivalence : ∀ {X} → Equivalence {X} _≡_
  equivalence = record { refl = refl; sym = sym; trans = trans }

--------------------------------------------------------------------------------
-- Natural numbers

module Nat where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ    #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  _+_ : ℕ → ℕ → ℕ
  zero  + y = y
  suc x + y = suc (x + y)

  open PropositionalEquality using (_≡_; refl; cong; equivalence)

  ≡-suc : ∀ {x y} → suc x ≡ suc y → x ≡ y
  ≡-suc refl = refl

  _≟_ : Decidable _≡_
  zero  ≟ zero  = left refl
  zero  ≟ suc y = right λ()
  suc x ≟ zero  = right λ()
  suc x ≟ suc y with x ≟ y
  ... | left  x≡y = left  (cong suc x≡y)
  ... | right x≢y = right (λ sx≡sy → x≢y (≡-suc sx≡sy))

  data _≤_ : Rel ℕ where
    z≤n : ∀ {n}   → zero ≤ n
    s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

  ≤-suc : ∀ {m n} → suc m ≤ suc n → m ≤ n
  ≤-suc (s≤s p) = p

  _≤?_ : Decidable _≤_
  zero  ≤? n     = left z≤n
  suc m ≤? zero  = right λ()
  suc m ≤? suc n with m ≤? n
  ... | left m≤n  = left  (s≤s m≤n)
  ... | right m>n = right (λ sm≤sn → m>n (≤-suc sm≤sn))

  antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
  antisym z≤n       z≤n       = refl
  antisym (s≤s m≤n) (s≤s n≤m) = cong suc (antisym m≤n n≤m)

  trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  trans z≤n       _         = z≤n
  trans (s≤s x≤y) (s≤s y≤z) = s≤s (trans x≤y y≤z)

  total : ∀ x y → Either (x ≤ y) (y ≤ x)
  total zero _ = left z≤n
  total (suc x) zero = right z≤n
  total (suc x) (suc y) with total x y
  ... | left x≤y  = left  (s≤s x≤y)
  ... | right y≤x = right (s≤s y≤x)

  reflexive : ∀ {x y} → x ≡ y → x ≤ y
  reflexive {zero}  refl = z≤n
  reflexive {suc x} refl = s≤s (reflexive {x} refl)

  totalOrder : TotalOrder _≡_ _≤_
  totalOrder = record
    { antisym     = antisym
    ; trans       = trans
    ; total       = total
    ; reflexive   = reflexive
    ; equivalence = equivalence
    }

  open Sort _≟_ _≤?_ totalOrder using (isort; treeSort)
