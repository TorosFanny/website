\begin{code}
module AgdaSort2 where

open import Data.Empty renaming (⊥ to Empty; ⊥-elim to absurd)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
import Function.Bijection as Bijection
import Level
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; setoid)
open import Relation.Nullary

-- We want to make things a bit simpler
Rel₀ : Set → Set₁
Rel₀ X = Rel X Level.zero

_↔_ : Set → Set → Set
A ↔ B = Bijection.Bijection (setoid A) (setoid B)

infix  2 _□
infixr 2 _↔⟨_⟩_

_□ : ∀ A → A ↔ A
_ □ = Bijection.id

_↔⟨_⟩_ : ∀ A {B C} → A ↔ B → B ↔ C → A ↔ C
A ↔⟨ A↔B ⟩ B↔C = B↔C Bijection.∘ A↔B

module Sort {X : Set} {_≈_ _≤_ : Rel₀ X} (ord : IsTotalOrder _≈_ _≤_) where
  open IsTotalOrder ord using (total)

  data ⊥X⊤ : Set where
    ⊤ ⊥ : ⊥X⊤
    ⟦_⟧ : X → ⊥X⊤

  data _≤̂_ : Rel₀ ⊥X⊤ where
    ⊥≤̂     : ∀ {x} → ⊥ ≤̂ x
    ≤̂⊤     : ∀ {x} → x ≤̂ ⊤
    ≤-lift : ∀ {x y} → x ≤ y → ⟦ x ⟧ ≤̂ ⟦ y ⟧

  data OList (l u : ⊥X⊤) : Set where
    nil  : l ≤̂ u → OList l u
    cons : ∀ x (xs : OList ⟦ x ⟧ u) → l ≤̂ ⟦ x ⟧ → OList l u

  data Parity : Set where p₀ p₁ : Parity

  data Tree (l u : ⊥X⊤) : ℕ → Set where
    empty  : l ≤̂ u → Tree l u 0
    2-node : ∀ {n} → (x : X) → Tree l ⟦ x ⟧ n → Tree ⟦ x ⟧ u n → Tree l u (suc n)
    3-node : ∀ {n} → (x y : X) →
             Tree l ⟦ x ⟧ n → Tree ⟦ x ⟧ ⟦ y ⟧ n → Tree ⟦ y ⟧ u n → Tree l u (suc n)

  data Insert (l u : ⊥X⊤) (n : ℕ) : Set where
    2-node : (x : X) → Tree l ⟦ x ⟧ n → Tree ⟦ x ⟧ u n → Insert l u n
    tree   : Tree l u n → Insert l u n

  insert : ∀ {l u n} → (x : X) → Tree l u n → l ≤̂ ⟦ x ⟧ → ⟦ x ⟧ ≤̂ u → Insert l u n

  insert x (empty l≤u) l≤x x≤u = 2-node x (empty l≤x) (empty x≤u)

  insert x (2-node y ly yu) l≤x x≤u with total x y
  insert x (2-node y ly yu) l≤x x≤u | inj₁ x≤y with insert x ly l≤x (≤-lift x≤y)
  insert x (2-node y ly yu) l≤x x≤u | inj₁ x≤y | 2-node z lz zy =
    tree (3-node z y lz zy yu)
  insert x (2-node y ly yu) l≤x x≤u | inj₁ x≤y | tree ly′ = tree (2-node y ly′ yu)
  insert x (2-node y ly yu) l≤x x≤u | inj₂ y≤x with insert x yu (≤-lift y≤x) x≤u
  insert x (2-node y ly yu) l≤x x≤u | inj₂ y≤x | 2-node z yz zu =
    tree (3-node y z ly yz zu)
  insert x (2-node y ly yu) l≤x x≤u | inj₂ y≤x | tree yu′ = tree (2-node y ly yu′)

  insert x (3-node y z ly yz zu) l≤x x≤u with total x y
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₁ x≤y
    with insert x ly l≤x (≤-lift x≤y)
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₁ x≤y | 2-node k lk ky =
    2-node y (2-node k lk ky) (2-node z yz zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₁ x≤y | tree ly′ =
    tree (3-node y z ly′ yz zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₂ y≤x with total x z
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₂ y≤x | inj₁  x≤z
    with insert x yz (≤-lift y≤x) (≤-lift x≤z)
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₂ y≤x | inj₁  x≤z | 2-node k yk kz =
    2-node k (2-node y ly yk) (2-node z kz zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₂ y≤x | inj₁  x≤z | tree yz′ =
    tree (3-node y z ly yz′ zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₂ y≤x | inj₂ z≤x
    with insert x zu (≤-lift z≤x) x≤u
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₂ y≤x | inj₂ z≤x | 2-node k zk ku =
    2-node z (2-node y ly yz) (2-node k zk ku)
  insert x (3-node y z ly yz zu) l≤x x≤u | inj₂ y≤x | inj₂ z≤x | tree zu′ =
    tree (3-node y z ly yz zu′)

  _⇒_++_ : ∀ {l u} x → OList l ⟦ x ⟧ → OList ⟦ x ⟧ u → OList l u
  x ⇒ nil l≤u       ++ xu = cons x xu l≤u
  x ⇒ cons y yx l≤y ++ xu = cons y (x ⇒ yx ++ xu) l≤y

  flatten : ∀ {l u n} → Tree l u n → OList l u
  flatten (empty l≤u)           = nil l≤u
  flatten (2-node x lx xu)      = x ⇒ flatten lx ++ flatten xu
  flatten (3-node x y lx xy yu) = x ⇒ flatten lx ++ (y ⇒ flatten xy ++ flatten yu)

  -- AnyT : ∀ {l u n} → (X → Set) → Tree l u n → Set
  -- AnyT P (empty _)             = Empty
  -- AnyT P (2-node x lx xu)      = P x ⊎ AnyT P lx ⊎ AnyT P xu
  -- AnyT P (3-node x y lx xy yu) = P x ⊎ P y ⊎ AnyT P lx ⊎ AnyT P xy ⊎ AnyT P yu

  -- _∈T_ : ∀ {l u n} → X → Tree l u n → Set
  -- x ∈T t = AnyT (λ y → x ≡ y) t

  -- AnyO : ∀ {l u} → (X → Set) → OList l u → Set
  -- AnyO P (nil _)       = Empty
  -- AnyO P (cons x xs _) = P x ⊎ AnyO P xs

  -- AnyO-++ : (P : X → Set) →
  --           ∀ {l u} x → (lx : OList l ⟦ x ⟧) → (xu : OList ⟦ x ⟧ u) →
  --           AnyO P (x ⇒ lx ++ xu) ↔ P x ⊎ AnyO P lx ⊎ AnyO P xu
  -- AnyO-++ = {!!}

  -- _∈O_ : ∀ {l u} → X → OList l u → Set
  -- x ∈O xs = AnyO (λ y → x ≡ y) xs

  -- flatten-lemma : ∀ {l u n} (t : Tree l u n) → ∀ z → (z ∈O flatten t) ↔ (z ∈T t)
  -- flatten-lemma (empty _) z = Empty □
  -- flatten-lemma (2-node x lx xu) z =
  --   (z ∈O (x ⇒ flatten lx ++ flatten xu)) ↔⟨ {!AnyO-++ {!!}!} ⟩
  --   (z ≡ x ⊎ z ∈O flatten lx ⊎ x ∈O flatten xu)                       ↔⟨ {!!} ⟩
  --   (z ≡ x ⊎ z ∈T lx ⊎ z ∈T xu) □
  -- flatten-lemma (3-node x y t t₁ t₂) z = {!!}

\end{code}
