\begin{code}
module AgdaSort2 where

open import AgdaSort
open Nat using (ℕ; zero; suc)

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

module Sort2 {X} {_≈_ _≤_ : Rel X}
            (_≤?_ : Decidable _≤_) (ord : TotalOrder _≈_ _≤_) where
  open TotalOrder ord using (trans; total; reflexive; equivalence)
  open Equivalence equivalence using (refl)
  open Sort _≤?_ ord using (⊥X⊤; ⊤; ⊥; ⟦_⟧; _≤̂_; ⊥≤̂; ≤̂⊤; ≤-lift)

  data Parity : Set where p₀ p₁ : Parity

  data Tree (l u : ⊥X⊤) : ℕ → Set where
    empty  : l ≤̂ u → Tree l u 0
    2-node : (x : X) → Tree l ⟦ x ⟧ → Tree ⟦ x ⟧ u → Tree l u
    3-node : (x y : X) → Tree l ⟦ x ⟧ → Tree ⟦ x ⟧ ⟦ y ⟧ → Tree ⟦ y ⟧ u → Tree l u

  -- ≤̂-trans : ∀ {l x u} → l ≤̂ x → x ≤̂ u → l ≤̂ u
  -- ≤̂-trans ⊥≤̂ _ = ⊥≤̂
  -- ≤̂-trans _ ≤̂⊤ = ≤̂⊤
  -- ≤̂-trans (x≤̂y l≤x) (x≤̂y x≤u) = x≤̂y (trans l≤x x≤u)

  data Insert (l u : ⊥X⊤) : Set where
    2-node : (x : X) → Tree l ⟦ x ⟧ → Tree ⟦ x ⟧ u → Insert l u
    tree   : Tree l u → Insert l u

  insert : ∀ {l u} → (x : X) → Tree l u → l ≤̂ ⟦ x ⟧ → ⟦ x ⟧ ≤̂ u → Insert l u
  insert x (empty l≤u) l≤x x≤u = tree (2-node x (empty l≤x) (empty x≤u))
  insert x (2-node y ly yu) l≤x x≤u with total x y
  insert x (2-node y ly yu) l≤x x≤u | left  x≤y with insert x ly l≤x (≤-lift x≤y)
  insert x (2-node y ly yu) l≤x x≤u | left  x≤y | 2-node z lz zy =
    tree (3-node z y lz zy yu)
  insert x (2-node y ly yu) l≤x x≤u | left  x≤y | tree ly′ = tree (2-node y ly′ yu)
  insert x (2-node y ly yu) l≤x x≤u | right y≤x with insert x yu (≤-lift y≤x) x≤u
  insert x (2-node y ly yu) l≤x x≤u | right y≤x | 2-node z yz zu =
    tree (3-node y z ly yz zu)
  insert x (2-node y ly yu) l≤x x≤u | right y≤x | tree yu′ = tree (2-node y ly yu′)
  insert x (3-node y z ly yz zu) l≤x x≤u with total x y
  insert x (3-node y z ly yz zu) l≤x x≤u | left  x≤y
    with insert x ly l≤x (≤-lift x≤y)
  insert x (3-node y z ly yz zu) l≤x x≤u | left  x≤y | 2-node k lk ky =
    2-node y (2-node k lk ky) (2-node z yz zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | left  x≤y | tree ly′ =
    tree (3-node y z ly′ yz zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | right y≤x with total x z
  insert x (3-node y z ly yz zu) l≤x x≤u | right y≤x | left  x≤z
    with insert x yz (≤-lift y≤x) (≤-lift x≤z)
  insert x (3-node y z ly yz zu) l≤x x≤u | right y≤x | left  x≤z | 2-node k yk kz =
    2-node k (2-node y ly yk) (2-node z kz zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | right y≤x | left  x≤z | tree yz′ =
    tree (3-node y z ly yz′ zu)
  insert x (3-node y z ly yz zu) l≤x x≤u | right y≤x | right z≤x
    with insert x zu (≤-lift z≤x) x≤u
  insert x (3-node y z ly yz zu) l≤x x≤u | right y≤x | right z≤x | 2-node k zk ku =
    2-node z (2-node y ly yz) (2-node k zk ku)
  insert x (3-node y z ly yz zu) l≤x x≤u | right y≤x | right z≤x | tree zu′ =
    tree (3-node y z ly yz zu′)

  insert′ : ∀ {l u} → (x : X) → Tree l u → l ≤̂ ⟦ x ⟧ → ⟦ x ⟧ ≤̂ u → Tree l u
  insert′ x lu l≤x x≤u with insert x lu l≤x x≤u
  ... | tree lu′       = lu′
  ... | 2-node y ly yu = 2-node y ly yu

\end{code}
