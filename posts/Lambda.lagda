In the [previous Agda example](/posts/AgdaSort.html) we saw how we can
approach the task of verifying a sorting function.  This time, we are
going to write a type checker for the simply typed λ-calculus, plus a
simple optimization on said terms that we will prove correct.  As in the
other post the bulk of the thinking has been done by other people.  The
type checking is a modified version of an example by Conor
McBride,[^tvftl] while the optimisation is taken from a talk given by
Adam Chlipala at POPL 2013---his Coq book [*Certified Programming with
Dependent Types*](http://adam.chlipala.net/cpdt/) contains many similar
examples.

[^tvftl]: See *The View from the Left*, and also the Agda version by Ulf
Norell in his *Programming in Agda* tutorial.

Let's get started.

## Useful imports

\begin{code}
module Lambda where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ≤)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary
open import Function
\end{code}

After the module declaration, we include some useful modules from the [Agda
standard
library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary):

* `Data.Nat` defines natural numbers.

* `Data.Fin` defines an inductive families to represent the type of all
  numbers less than a given number.  For instance `Fin 3` will be
  inhabited by `0`, `1`, and `2`.

* `Data.List`, predictably, defines finite lists.

* `Data.Vec` defines lists indexed by their length.  This allows, for
  example, for safe indexing of elements.

* `Relation.Binary.PropositionalEquality` defines propositional equality as
  [presented](/posts/AgdaSort.html#propositional-equality) in the previous post.
  `cong₂` is the two-argument version of `cong`.

* `Function` exports some common utilities regarding functions that
  should be familiar to the Haskell programmer, such as function
  composition.

## Simple types and raw terms

\begin{code}
infixr 30 _⇒_
data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

≡⇒₁ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → σ ≡ σ′
≡⇒₁ refl = refl

≡⇒₂ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → τ ≡ τ′
≡⇒₂ refl = refl

_≟_ : Decidable {A = Type} _≡_
nat   ≟ nat   = yes refl
nat   ≟ _ ⇒ _ = no λ()
_ ⇒ _ ≟ nat   = no λ()
σ ⇒ τ ≟ σ′ ⇒ τ′ with σ ≟ σ′ | τ ≟ τ′
σ ⇒ τ ≟ .σ ⇒ .τ | yes refl | yes refl = yes refl
σ ⇒ τ ≟ .σ ⇒ τ′ | yes refl | no τ≢τ′  = no (τ≢τ′ ∘ ≡⇒₂)
σ ⇒ τ ≟ σ′ ⇒ τ′ | no  σ≢σ′ | _        = no (σ≢σ′ ∘ ≡⇒₁)

infixl 80 _·_
data Raw : Set where
  var : ℕ → Raw
  lit : ℕ → Raw
  _⊕_ : Raw → Raw → Raw
  _·_ : Raw → Raw → Raw
  lam : Type → Raw → Raw
\end{code}

## Typed terms, and type inference

\begin{code}
Ctx = Vec Type

data Term {n} (Γ : Ctx n) : Type → Set where
  var : ∀ {τ} (v : Fin n) → τ ≡ lookup v Γ → Term Γ τ
  lit : ℕ → Term Γ nat
  _⊕_ : Term Γ nat → Term Γ nat → Term Γ nat
  _·_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

erase : ∀ {n} {Γ : Ctx n} {τ} → Term Γ τ → Raw
erase (var v _) = var (toℕ v)
erase (lit n) = lit n
erase (t ⊕ u) = erase t ⊕ erase u
erase (t · u) = erase t · erase u
erase (lam σ t) = lam σ (erase t)

data Fromℕ (n : ℕ) : ℕ → Set where
  yes : (m : Fin n) → Fromℕ n (toℕ m)
  no  : (m : ℕ)     → Fromℕ n (n + m)

fromℕ : (n m : ℕ) → Fromℕ n m
fromℕ zero  m = no m
fromℕ (suc n) zero = yes zero
fromℕ (suc n) (suc m) with fromℕ n m
fromℕ (suc n) (suc .(toℕ m)) | yes m = yes (suc m)
fromℕ (suc n) (suc .(n + m)) | no  m = no m

data Infer {n} (Γ : Ctx n) : Raw → Set where
  ok  : (τ : Type) (t : Term Γ τ) → Infer Γ (erase t)
  bad : {e : Raw} → Infer Γ e

infer : ∀ {n} (Γ : Ctx n) (e : Raw) → Infer Γ e
infer {n} Γ (var v) with fromℕ n v
infer {n} Γ (var .(toℕ v)) | yes v = ok (lookup v Γ) (var v refl)
infer {n} Γ (var .(n + m)) | no  m = bad
infer Γ (lit n) = ok nat (lit n)
infer Γ (t ⊕ u) with infer Γ t | infer Γ u
infer Γ (.(erase t) ⊕ .(erase u)) | ok nat t  | ok nat u = ok nat (t ⊕ u)
infer Γ (_ ⊕ _)                   | _         | _        = bad
infer Γ (t · u) with infer Γ t | infer Γ u
infer Γ (.(erase t) · .(erase u)) | ok (σ ⇒ τ) t | ok σ′ u with σ ≟ σ′
infer Γ (.(erase t) · .(erase u)) | ok (σ ⇒ τ) t | ok .σ u | yes refl = ok τ (t · u)
infer Γ (.(erase t) · .(erase u)) | ok (σ ⇒ τ) t | ok σ′ u | no  _    = bad
infer Γ (.(erase t) · u)          | ok _ t       | _       = bad
infer Γ (_ · _)                   | bad          | _       = bad
infer Γ (lam σ e) with infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ e)          | bad    = bad

\end{code}

## Embedding terms

\begin{code}
⟦_⟧ : Type → Set
⟦ nat   ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _∷_
data Env : ∀ {n} → Ctx n → Set where
  []  : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookupEnv : ∀ {n} {Γ : Ctx n} → (m : Fin n) → Env Γ → ⟦ lookup m Γ ⟧
lookupEnv zero    (x ∷ _)   = x
lookupEnv (suc n) (_ ∷ env) = lookupEnv n env

_[_] : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var v refl ] = lookupEnv v env
env [ lit n      ] = n
env [ t ⊕ u      ] = env [ t ] + env [ u ]
env [ t · u      ] = (env [ t ]) (env [ u ])
env [ lam _ t    ] = λ x → (x ∷ env) [ t ]
\end{code}

## Constant folding

\begin{code}
--------------------------------------------------------------------------------
-- Simple constant folding, plus a proof that the operation preserves the
-- denotation.  Note that we mix proof and folding because this makes the proof
-- much quicker due to how pattern matching works in Agda.

-- yeee
postulate ext : ∀ {A B : Set} {f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g

record Optimised {n} {Γ : Ctx n} {σ} (t : Term Γ σ) : Set where
  constructor opt
  field
    optimised : Term Γ σ
    preserves : ∀ {env} → env [ t ] ≡ env [ optimised ]

cfold : ∀ {n} {Γ : Ctx n} {τ} (t : Term Γ τ) → Optimised t
cfold (var v p) = opt (var v p) refl
cfold (t · u) with cfold t | cfold u
... | opt t′ p | opt u′ q = opt (t′ · u′) (cong₂ (λ t u → t u) p q)
cfold (lam σ t) with cfold t
... | opt t′ p = opt (lam σ t′) (ext p)
cfold (t ⊕ u) with cfold t | cfold u
cfold (t ⊕ u) | opt (lit n) p | opt (lit m) q = opt (lit (n + m)) (cong₂ _+_ p q)
cfold (t ⊕ u) | opt t′ p | opt u′ q = opt (t′ ⊕ u′) (cong₂ _+_ p q)
cfold (lit x) = opt (lit x) refl

\end{code}
