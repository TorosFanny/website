In the [previous Agda example](/posts/AgdaSort.html) we saw how we can approach
the task of verifying a sorting function.  This time, we are going to write a
type checker for the simply typed λ-calculus, plus a simple optimization on said
terms that we will prove correct.  As in the other post the bulk of the thinking
has been done by other people: I took the type checking part from [Ulf Norell's
Agda tutorial](http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf), and
the term transformation example from [Adam Chlipala's Coq book 'Certified
Programming with Dependent Types'](http://adam.chlipala.net/cpdt/).  They are
both great, go read them if you have time!

Let's get started.

## Useful imports

\begin{code}
module Lambda where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Function hiding (_$_; const)
\end{code}

After the module declaration, we include some useful modules from the [Agda
standard
library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary):

* `Data.Nat` defines natural numbers, we only import the type (`ℕ`) and
  constructors (`zero` and `suc`), and the addition operator.
* `Data.List` defines finite lists, again we import type and constructors, plus
  `length`.
* `Relation.Binary.PropositionalEquality` defines propositional equality as
  [presented](/posts/AgdaSort.html#propositional-equality) in the previous post.
  `cong₂` is the two-argument version of `cong`.
* `Function` exports some common utilities that should be familiar to the
  Haskell programmer.  We hide two of them because they would conflict with the
  names we will be defining.

## Indexing things

\begin{code}
data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x l}           → x ∈ (x ∷ l)
  there : ∀ {x l y} → x ∈ l → x ∈ (y ∷ l)

index : ∀ {A} {x : A} {xs} → x ∈ xs → ℕ
index here      = zero
index (there p) = suc (index p)

data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside  : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

lookup : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
lookup []       n    = outside n
lookup (x ∷ xs) zero = inside x here
lookup (x ∷ xs) (suc n) with lookup xs n
lookup (x ∷ xs) (suc .(index p))       | inside y p = inside y (there p)
lookup (x ∷ xs) (suc .(length xs + n)) | outside n  = outside n

infixr 30 _⇒_
data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

data Equal? : Type → Type → Set where
  yes : ∀ {τ}   → Equal? τ τ
  no  : ∀ {σ τ} → Equal? σ τ

_≟_ : (σ τ : Type) → Equal? σ τ
nat   ≟ nat   = yes
nat   ≟ _ ⇒ _ = no
_ ⇒ _ ≟ nat   = no
σ ⇒ τ ≟ σ′ ⇒ τ′ with σ ≟ σ′ | τ ≟ τ′
σ ⇒ τ ≟ .σ ⇒ .τ | yes | yes = yes
_ ⇒ _ ≟ _  ⇒ _  | _   | _   = no

--------------------------------------------------------------------------------
-- Raw terms

infixl 80 _$_
data Raw : Set where
  var   : ℕ → Raw
  const : ℕ → Raw
  _⊕_   : Raw → Raw → Raw
  _$_   : Raw → Raw → Raw
  lam   : Type → Raw → Raw


--------------------------------------------------------------------------------
-- Typed terms

Ctx = List Type

data Term (Γ : Ctx) : Type → Set where
  var   : ∀ {τ} → τ ∈ Γ → Term Γ τ
  const : ℕ → Term Γ nat
  _⊕_   : Term Γ nat → Term Γ nat → Term Γ nat
  _$_   : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam   : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (var x) = var (index x)
erase (const n) = const n
erase (t ⊕ u) = erase t ⊕ erase u
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)


data Infer (Γ : Ctx) : Raw → Set where
  ok  : (τ : Type) (t : Term Γ τ) → Infer Γ (erase t)
  bad : {e : Raw} → Infer Γ e

infer : (Γ : Ctx) (e : Raw) → Infer Γ e
infer Γ (var n) with            lookup Γ n
infer Γ (var .(length Γ + n)) | outside n  = bad
infer Γ (var .(index x))      | inside σ x = ok σ (var x)
infer Γ (const n) = ok nat (const n)
infer Γ (t ⊕ u) with                infer Γ t | infer Γ u
infer Γ (.(erase t) ⊕ .(erase u)) | ok nat t  | ok nat u = ok nat (t ⊕ u)
infer Γ (_ ⊕ _)                   | _         | _        = bad
infer Γ (t $ u) with                infer Γ t    | infer Γ u
infer Γ (.(erase t) $ .(erase u)) | ok (σ ⇒ τ) t | ok σ′ u with σ ≟ σ′
infer Γ (.(erase t) $ .(erase u)) | ok (σ ⇒ τ) t | ok .σ u | yes = ok τ (t $ u)
infer Γ (.(erase t) $ .(erase u)) | ok (σ ⇒ τ) t | ok σ′ u | no  = bad
infer Γ (.(erase t) $ u)          | ok _ t       | _       = bad
infer Γ (_ $ _)                   | bad          | _       = bad
infer Γ (lam σ e) with       infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ e)          | bad    = bad

--------------------------------------------------------------------------------
-- Embedding of types and terms

⟦_⟧ : Type → Set
⟦ nat   ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _◁_
data Env : List Type → Set where
  ε   : Env []
  _◁_ : ∀ {τ τs} → ⟦ τ ⟧ → Env τs → Env (τ ∷ τs)

_!_ : ∀ {τ τs} → τ ∈ τs → Env τs → ⟦ τ ⟧
here       ! (x ◁ _) = x
there x∈xs ! (_ ◁ l) = x∈xs ! l

_[_] : ∀ {Γ τ} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var x   ] = x ! env
env [ const n ] = n
env [ t ⊕ u   ] = env [ t ] + env [ u ]
env [ t $ u   ] = (env [ t ]) (env [ u ])
env [ lam _ t ] = λ x → (x ◁ env) [ t ]

--------------------------------------------------------------------------------
-- Simple constant folding, plus a proof that the operation preserves the
-- denotation.  Note that we mix proof and folding because this makes the proof
-- much quicker due to how pattern matching works in Agda.

-- yeee
postulate ext : ∀ {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

record Transformation {Γ σ} (t : Term Γ σ) : Set where
  constructor trans
  field
    result    : Term Γ σ
    preserves : ∀ {c} → c [ t ] ≡ c [ result ]
open Transformation

cfold′ : ∀ {Γ σ} → (t : Term Γ σ) → Transformation t
cfold′ (var v) = trans (var v) refl
cfold′ (const n) = trans (const n) refl
cfold′ (t $ u) with cfold′ t | cfold′ u
... | trans t′ p | trans u′ q = trans (t′ $ u′) (cong₂ (λ x y → x y) p q)
cfold′ (lam σ t) with cfold′ t
... | trans t′ p = trans (lam σ t′) (ext (λ x → p))
cfold′ (t ⊕ u) with cfold′ t | cfold′ u
... | trans (const n) p | trans (const m) q = trans (const (n + m)) (cong₂ _+_ p q)
... | trans t′        p | trans u′        q = trans (t′ ⊕ u′)       (cong₂ _+_ p q)

cfold : ∀ {Γ σ} → Term Γ σ → Term Γ σ
cfold = result ∘ cfold′

\end{code}
