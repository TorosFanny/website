---
title: Agda by Example: Sorting
date: 2013-03-25
---

## Dependent types?  Agda?

The Haskell programmer is used to the pleasure of collaborating with a nice type
system.  Haskell itself hits quite a sweet spot of expressivity and
manageability---type inference is (mostly) decidable, no subtyping, etc.
However, in the past 30 years, new systems have been emerging that allow the
user to encode many more properties at the type level.  In fact, these systems
are so expressive that they are often used as logical frameworks to prove
theorems rather than to write programs, and are thus called 'theorem provers'
rather than 'programming languages'.  Thanks to
[a notorious correspondence](https://en.wikipedia.org/wiki/Curry-Howard), we
know that these two activities are really the same.  This kind of type systems
are often said to have *dependent types*, since types, as we will see, can
depend on values.

[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php) is one of the most
prominent systems of this kind at the moment.  Many functional programmers like
it because it's has very 'functional' slant, trying to do everything with
'simple' programming rather than recurring to mechanised transformation of terms
(of which [Coq](http://coq.inria.fr/) is the most famous offender).  In this
blog I will try to give some examples that will hopefully make you interested.
In this first post we are going to write two sorting algorithms, and prove that
they return a sorted list.  The implementation is taken from a
[presentation](https://personal.cis.strath.ac.uk/~conor/Pivotal.pdf) by Conor
McBride, adapted for Agda.

This is a literate Agda file---you should be able to paste it in a file called
`AgdaSort.lagda` and you should be ready for type checking.  I'm not going to
explain how to install agda here, you can refer to the
[wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php) or the wonderful
[freenode channel](irc://chat.freenode.net/haskell).

\begin{code}
module AgdaSort where
\end{code}

## Agda lists

Let's warm up by defining a data type dear to Haskell, a functional list:

\begin{code}
infixr 5 _∷_
data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X
\end{code}

The syntax to declare this type resembles the syntax for
[GADTs](https://en.wikibooks.org/wiki/Haskell/GADT) in Haskell.  Here `X` is the
parametrised type---what Agda calls `Set` is more or less what Haskell calls
`*`, the type of types, or 'kind' in Haskell parlance.  `List` is a type
constructor which takes a type and 'returns' a new type---`List : Set →
Set`---much like Haskell's `[]`---`[] : * → *`.

Then we have two constructors, `[]` for an empty list and `_∷_` to cons an
element to an existing list.  Agda gives us great flexibility in the syntax:
arbitrary operators can defined where `_` indicates an argument.  In this case
`_∷_` is a binary operator.  The fixity declaration is similar to what we would
find in Haskell.

Let's define `foldr`:

\begin{code}
foldr : ∀ {A} {B : Set} → (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (a ∷ as) = f a (foldr f b as)
\end{code}

Nothing surprising here, apart from the fact that we have to take the trouble of
bringing the type variables into scope manually.  In Agda, things in curly
braces are implicit and the type checker will try to infer them by unification.
Here we are also omitting the type of `A` by using `∀`---we can do this since
`A` is an argument to `List` later in the signature.  For the converse reason we
must provide a type for `B`.

## Sum and products

Now another 'boring' type, 'Either', plus the associated destructor ('either' in
Haskell):

\begin{code}
data Either (A : Set) (B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

[_,_] : ∀ {A B} {C : Set} → (A → C) → (B → C) → Either A B → C
[ f , g ] (left x)  = f x
[ f , g ] (right x) = g x
\end{code}

And `_∧_`, corresponding to Haskell's binary tuple:

\begin{code}
infixr 2 _∧_
infixr 4 _,_
record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
\end{code}

When possible it's generally a good idea to define data types as records, since
Agda will know more things about them [^etalaws] and can infer values of record
types more easily too.  The syntax is quite straightforward---we define a
constructor `_,_` and fields accessors `fst` and `snd`.

[^etalaws]: Most notably, the Agda typechecker will be able to use the η--law `x
= fst x , snd x` if needed.

## `Unit` and `Empty`

Now let's start doing something that we can't do in Haskell.  First we define
a datatype with one inhabitant, much like `()` in Haskell:

\begin{code}
record Unit : Set where
  constructor tt
\end{code}

Now for a type with no inhabitants---no constructors:

\begin{code}
data Empty : Set where
\end{code}

What is `Empty` useful for?  Well, if the user provides a term of type `Empty`,
we can give back anything he might want---corresponding to the logical *ex falso
quodlibet*.

\begin{code}
absurd : {X : Set} → Empty → X
absurd ()
\end{code}

The `()` is what is called an 'empty pattern': Agda knows that no closed term
will be of type `Empty`, and thus lets us leave out the body of functions with
arguments of that type.  Note that in Haskell we can easily get terms of *any*
type in various ways, the most straightforward being general recursion:

```haskell
undefined :: forall a. a
undefined = undefined
```

Agda makes sure that this is not possible [^consistent], thus keeping the system
*consistent*.  This has very pleasant consequences, the heaviest being that all
programs terminate.  For this reason consistent systems must be
Turing--incomplete (we can't write an infinite loops!), and thus Agda lets us
'step out' of these checks if we want to, although it is rarely needed---most
algorithms we write are quite easily provably terminating.  Note that
consistency was not put in Agda to please mathematicians (or not only anyway):
given the expressivity of the type system type checking and evaluation are
tightly intertwined, and thus we can send the compiler in an infinite loop if we
can write one.

[^consistent]: Specifically:
    * Functions must be *structurally recursive*, where the arguments in the
      recursive calls are decreasing.
    * Disallows data type declarations that are not *strictly positive* , for
      example the infamous `data Mu f = Mu (f (Mu f))` in Haskell.
    * Has a hierarchy of types---more on this later.

We can also define something close to negation in logic:

\begin{code}
infix 3 ¬_
¬_ : Set → Set
¬ X = X → Empty
\end{code}

We would expect terms of type `¬ (3 > 4)` to exist.  Here it starts being clear
that types are very 'first class' in Agda---functions can work on them as they
do with ordinary values: in this case `¬` takes a type and forms another one.

## Different `Rel`ations

We need one last ingredient before we can start sorting things.  We *could*
write our sort for some specific data type, say integers, but why would we do
that considering that we have a language that lets us express abstract
structures in a really nice way?

First we give a general definition of a binary relation on a type `X`:

\begin{code}
Rel : Set → Set₁
Rel X = X → X → Set
\end{code}

The `Set₁` indicates that a relation between two `Set`s is 'larger' than a `Set`
itself---this is nothing to worry about now but it follows a tradition in set
theory that goes back to Russell to avoid paradoxes [^girards].  `Set` is in
fact a shorthand for `Set₀` and represent the type of types of values: `Unit :
Set₀ : Set₁ : Set₂ : ...`.

[^girards]: In type theory this is known as Hurkens' paradox, you can find an
Agda (with `Set : Set` enabled) rendition
[here](http://code.haskell.org/Agda/test/succeed/Hurkens.agda).

Then we define the type of decidable relations---we would expect relations like
'less than' on integers or 'sortedness' on lists to be decidable:

\begin{code}
Decidable : ∀ {X} → Rel X → Set
Decidable R = ∀ x y → Either (R x y) (¬ (R x y))
\end{code}

That is, a decidable relation is a function that tells us if `x` and `y` are
related or not.

Now the interesting part.  To sort a list, we need two relations on the elements
of the list: some notion of equality and some ordering on the elements.  More
formally, the equality relation will be an *emph*
[equivalence](https://en.wikipedia.org/wiki/Equivalence_relation):

\begin{code}
record Equivalence {X : Set} (_≈_ : Rel X) : Set₁ where
  field
    refl  : ∀ {x}     → x ≈ x
    sym   : ∀ {x y}   → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
\end{code}

The definition on Wikipedia translates literally to Agda.  Same story for our
ordering, which will need to be
[total](https://en.wikipedia.org/wiki/Total_ordering):

\begin{code}
record TotalOrder {X : Set} (_≈_ : Rel X) (_≤_ : Rel X) : Set₁ where
  field
    antisym     : ∀ {x y}   → x ≤ y → y ≤ x → x ≈ y
    trans       : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    total       : ∀ x y     → Either (x ≤ y) (y ≤ x)
    reflexive   : ∀ {x y}   → x ≈ y → x ≤ y
    equivalence : Equivalence _≈_
\end{code}

## Sorting

We can finally begin to sort.  To do this we will define a *module* parametrised
over a type and an ordering.  Agda has a very flexible module system---in fact
we have already been using it by defining record, which are implicitly modules.

\begin{code}
module Sort {X : Set} {_≈_ _≤_ : Rel X}
            (_≈?_ : Decidable _≈_) (_≤?_ : Decidable _≤_)
            (ord : TotalOrder _≈_ _≤_) where
  open TotalOrder ord using (trans; total; reflexive; equivalence)
  open Equivalence equivalence using (refl)
\end{code}

We require both relations to be decidable, and we bring in scope some fields of
the records using `open`.

### Insertion sort

We want to represent bounded lists, but we want the bounds to be possible
'open'.  For this purpose we wrap our type `X` in a data type that contains a
'top' and 'bottom' elements, that are respectively greater or equal and lower or
equal than all the other elements.

\begin{code}
  data ⊥X⊤ : Set where
    ⊤ ⊥ : ⊥X⊤
    ⟦_⟧ : X → ⊥X⊤
\end{code}

For `⊥X⊤` to be useful, we lift our ordering to work with it:

\begin{code}
  _≤̂_ : ⊥X⊤ → ⊥X⊤ → Set
  ⊥     ≤̂ _     = Unit
  ⟦ n ⟧ ≤̂ ⟦ m ⟧ = n ≤ m
  _     ≤̂ ⊤     = Unit
  _     ≤̂ _     = Empty
\end{code}

...and a 'sandwiching' relation:

\begin{code}
  _≤_≤_ : ⊥X⊤ → X → ⊥X⊤ → Set
  l ≤ x ≤ u = l ≤̂ ⟦ x ⟧ ∧ ⟦ x ⟧ ≤̂ u
\end{code}

We can now define the type of bounded, ordered lists:

\begin{code}
  data OList (l u : ⊥X⊤) : Set where
    nil  : l ≤̂ u → OList l u
    cons : ∀ x (xs : OList ⟦ x ⟧ u) → l ≤ x ≤ u → OList l u
\end{code}

`nil` will work with any bounds, provided that the lower `l` is less or equal
than the upper `u`.  `cons` will cons an element `x` to a list with `x` as a
lower bound, and return a list with lower bound `l`, provided that `l ≤ x ≤ u`.

We can easily get a 'normal' list back from an `OList`:

\begin{code}
  toList : ∀ {l u} → OList l u → List X
  toList (nil _) = []
  toList (cons x xs _) = x ∷ toList xs
\end{code}

With the right data types, writing and proving correct [^sortcorrect] an
[insertion sort](https://en.wikipedia.org/wiki/Insertion_sort) is a breeze---I
encourage you to try and writing yourself checking the goals as you pattern
match, the only non--trivial case is the last one:

[^sortcorrect]: Some might complain that actually we are only proving half of
the story, since we need to guarantee that the result list is a permutation of
the input list to prove a sorting algorithm correct.  That is doable but a bit
more involved.  What is very easy is to prove that length is preserved, see
[this file](https://github.com/bitonic/agda-examples/blob/master/Sort.agda) for
a version of this article which does exactly that.

\begin{code}
  insert : ∀ {l u} → (x : X) (xs : OList l u) {l≤x≤u : l ≤ x ≤ u} →
           OList l u
  insert y (nil _) {l≤y , y≤u} = cons y (nil y≤u) (l≤y , y≤u)
  insert y (cons x xs (l≤x , x≤u)) with y ≤? x
  insert y (cons x xs (l≤x , x≤u)) {l≤y , y≤u} | left  y≤x =
    cons y (cons x xs (y≤x , x≤u)) (l≤y , y≤u)
  insert y (cons x xs (l≤x , x≤u)) {l≤y , y≤u} | right y>x =
    cons x (insert x xs {reflexive refl , x≤u}) (l≤x , x≤u)
\end{code}

Insertion sort is just a fold [^etafun]:

[^etafun]: The pointless amongst you will be horrified by the `λ x xs → insert x
xs`---however we need it, due to how implicit parameters work in Agda.

\begin{code}
  isort′ : List X → OList ⊥ ⊤
  isort′ = foldr (λ x xs → insert x xs) (nil _)

  isort : List X → List X
  isort xs = toList (isort′ xs)
\end{code}

Now for something more efficient, a [tree
sort](https://en.wikipedia.org/wiki/Tree_sort).  Firstly we'll define a bounded,
ordered binary tree:

\begin{code}
  data Tree (l u : ⊥X⊤) : Set where
    leaf : l ≤̂ u → Tree l u
    node : (x : X) → Tree l ⟦ x ⟧ → Tree ⟦ x ⟧ u → Tree l u
\end{code}

The technique is similar to that employed in `OList`.  Then we need a procedure
to insert an element in an existing tree:

\begin{code}
  newLeaf : ∀ {l u} → (x : X) → Tree l u → {l≤x≤u : l ≤ x ≤ u} → Tree l u
  newLeaf x (leaf _) {l≤x , x≤u} = node x (leaf l≤x) (leaf x≤u)
  newLeaf x (node y ly yu) with x ≤? y
  newLeaf x (node y ly yu) {l≤x , x≤u} | left x≤y =
    node y (newLeaf x ly {l≤x , x≤y}) yu
  newLeaf x (node y ly yu) {l≤x , x≤u} | right x>y  =
    node y ly (newLeaf x yu {[ (λ p → absurd (x>y p)) , (λ p → p) ] (total x y) , x≤u})
\end{code}

Again, the only tricky bit is the last one, where we need to convince Agda that
`y ≤ x` given that `¬ (x ≤ y)`.

Similar to `isort′`, turning a `List` into a `Tree` is a simple fold:

\begin{code}
  fromList : List X → Tree ⊥ ⊤
  fromList = foldr (λ x xs → newLeaf x xs) (leaf _)
\end{code}

Now we need to 'flatten' a `Tree` into an `OList`.  To do that we need a few
additional lemmas---first, transitivity for the lifted ordering, which is boring
but easy:

\begin{code}
  ≤̂-trans : ∀ l x u → l ≤̂ ⟦ x ⟧ → ⟦ x ⟧ ≤̂ u → l ≤̂ u
  ≤̂-trans ⊤     _ ⊤     _   _   = _
  ≤̂-trans ⊤     _ ⊥     _   ()
  ≤̂-trans ⊤     _ ⟦ _ ⟧ ()  _  
  ≤̂-trans ⊥     _ _     _   _   = _
  ≤̂-trans ⟦ _ ⟧ _ ⊤     _   _   = _
  ≤̂-trans ⟦ _ ⟧ _ ⊥     _   ()
  ≤̂-trans ⟦ l ⟧ x ⟦ u ⟧ l≤x x≤u = trans l≤x x≤u
\end{code}

Then, something that shows that the bounds of an ordered list are ordered correctly:

\begin{code}
  OList-≤ : ∀ {l u} → OList l u → l ≤̂ u
  OList-≤ (nil l≤u) = l≤u
  OList-≤ {l} {u} (cons x xu (l≤x , x≤u)) = ≤̂-trans l x u l≤x (OList-≤ xu)
\end{code}

Now we can define `OList` concatenation, with the twist of inserting a new
element in the middle; and finally `flatten`:

\begin{code}
  _⇒_++_ : ∀ {l u} → (x : X) → OList l ⟦ x ⟧ → OList ⟦ x ⟧ u → OList l u
  x ⇒ nil l≤u               ++ xu = cons x xu (l≤u , OList-≤ xu)
  x ⇒ cons y yx (l≤y , y≤x) ++ xu =
    cons y (x ⇒ yx ++ xu) (l≤y , ≤̂-trans ⟦ y ⟧ x _ y≤x (OList-≤ xu))
  flatten : ∀ {l u} → Tree l u → OList l u
  flatten (leaf l≤u) = (nil l≤u)
  flatten (node x lx xu) =  x ⇒ flatten lx ++ flatten xu
\end{code}

Then we are good with yet another fold.

\begin{code}
  treeSort′ : List X → OList ⊥ ⊤
  treeSort′ xs = flatten (foldr (λ x xs → newLeaf x xs) (leaf _) xs)

  treeSort : List X → List X
  treeSort xs = toList (treeSort′ xs)
\end{code}

Once 

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
\end{code}
