---
title: Agda by Example: Lambda calculus
date: 2013-04-01
---


\begin{code}
module Lambda where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Function hiding (_$_; const)

--------------------------------------------------------------------------------
-- List utilities

data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x l}           → x ∈ (x ∷ l)
  there : ∀ {x l y} → x ∈ l → x ∈ (y ∷ l)

index : ∀ {A} {x : A} {xs} → x ∈ xs → ℕ
index here      = zero
index (there p) = suc (index p)

data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside  : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

lookup : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
lookup []       n    = outside n
lookup (x ∷ xs) zero = inside x here
lookup (x ∷ xs) (suc n) with lookup xs n
lookup (x ∷ xs) (suc .(index p))       | inside y p = inside y (there p)
lookup (x ∷ xs) (suc .(length xs + n)) | outside n  = outside n


--------------------------------------------------------------------------------
-- Types and types equality

infixr 30 _⇒_
data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

data Equal? : Type → Type → Set where
  yes : ∀ {τ} → Equal? τ τ
  no  : ∀ {σ τ} → Equal? σ τ

_≟_ : (σ τ : Type) → Equal? σ τ
nat ≟ nat = yes
nat ≟ _ ⇒ _ = no
_ ⇒ _ ≟ nat = no
σ ⇒ τ ≟ σ′ ⇒ τ′ with σ ≟ σ′ | τ ≟ τ′
σ ⇒ τ ≟ .σ ⇒ .τ | yes | yes = yes
_ ⇒ _ ≟ _  ⇒ _  | _   | _   = no

--------------------------------------------------------------------------------
-- Raw terms

mutual
  infixl 80 _$_
  data Raw↑ : Set where
    var   : ℕ → Raw↑
    const : ℕ → Raw↑
    _⊕_   : Raw↓ → Raw↓ → Raw↑
    _$_   : Raw↑ → Raw↓ → Raw↑

  data Raw↓ : Set where
    lam : Raw↓ → Raw↓
    inf : Raw↑ → Raw↓


--------------------------------------------------------------------------------
-- Typed terms

Ctx = List Type

mutual
  data Term↑ (Γ : Ctx) : Type → Set where
    var   : ∀ {τ} → τ ∈ Γ → Term↑ Γ τ
    const : ℕ → Term↑ Γ nat
    _⊕_   : Term↓ Γ nat → Term↓ Γ nat → Term↑ Γ nat
    _$_   : ∀ {σ τ} → Term↑ Γ (σ ⇒ τ) → Term↓ Γ σ → Term↑ Γ τ

  data Term↓ (Γ : Ctx) : Type → Set where
    lam : ∀ σ {τ} → Term↓ (σ ∷ Γ) τ → Term↓ Γ (σ ⇒ τ)

mutual
  erase↑ : ∀ {Γ τ} → Term↑ Γ τ → Raw↑
  erase↑ (var v) = var (index v)
  erase↑ (const n) = const n
  erase↑ (t ⊕ u) = {!erase↓ t ⊕ erase↓ u!}
  erase↑ (t $ u) = {!!}

  erase↓ : ∀ {Γ τ} → Term↓ Γ τ → Raw↓
  erase↓ 

-- data Infer (Γ : Ctx) : Raw↑ → Set where
--   ok  : (τ : Type) (t : Term Γ τ) → Infer Γ (erase t)
--   bad : {e : Raw↑} → Infer Γ e


-- infer : (Γ : Ctx) (e : Raw) → Infer Γ e

-- infer Γ (var n) with            lookup Γ n
-- infer Γ (var .(length Γ + n)) | outside n  = bad
-- infer Γ (var .(index x))      | inside σ x = ok σ (var x)

-- infer Γ (const n) = ok nat (const n)

-- infer Γ (t ⊕ u) with                infer Γ t | infer Γ u
-- infer Γ (.(erase t) ⊕ .(erase u)) | ok nat t  | ok nat u = ok nat (t ⊕ u)
-- infer Γ (_ ⊕ _)                   | _         | _        = bad

-- infer Γ (t $ u) with                infer Γ t    | infer Γ u
-- infer Γ (.(erase t) $ .(erase u)) | ok (σ ⇒ τ) t | ok σ′ u with σ ≟ σ′
-- infer Γ (.(erase t) $ .(erase u)) | ok (σ ⇒ τ) t | ok .σ u | yes = ok τ (t $ u)
-- infer Γ (.(erase t) $ .(erase u)) | ok (σ ⇒ τ) t | ok σ′ u | no  = bad
-- infer Γ (.(erase t) $ u)          | ok _ t       | _       = bad
-- infer Γ (_ $ _)                   | bad          | _       = bad

-- infer Γ (lam σ e) with       infer (σ ∷ Γ) e
-- infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
-- infer Γ (lam σ e)          | bad    = bad

\end{code}
