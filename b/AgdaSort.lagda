---
title: Agda by Example: Sorting
date: 2013-03-25
---

## Agda?

The Haskell programmer is used to the pleasure of collaborating with a nice type
system.  Haskell itself hits quite a sweet spot of expressivity and
manageability---type inference is (mostly) decidable, no subtyping, etc.
However, in the past 30 years, new systems have been emerging that allow the
user to encode many more properties at the type level.  In fact, these systems
are so expressive that they are often used as logical frameworks for mathematics
rather than to write programs, and are thus often called 'theorem provers'
rather than 'programming languages'.  Thanks to [a notorious
correspondence](https://en.wikipedia.org/wiki/Curry-Howard), we know that these
two activities are really the same [^itt].

[^itt]: The roof of most of said systems is [Intuitionistic Type
Theory](https://en.wikipedia.org/wiki/Intuitionistic_type_theory).

[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php) is one of the most
prominent systems of this kind at the moment.  Many Haskell programmers like it
because it's has very 'functional' slant, doing everything with 'pure'
programming rather than recurring to mechanised transformation of terms (of
which [Coq](http://coq.inria.fr/) is the most famous offender).  In this blog I
will try to give some examples that will hopefully make you interested.  This
first post explains how sorting algorithms can be proven correct.  The
implementation follows a
[presentation](https://personal.cis.strath.ac.uk/~conor/Pivotal.pdf) by Conor
McBride.

This is a literate Agda file---you should be able to paste it in a file called
`AgdaSort.lagda` and typecheck it.  I'm not going to explain how to install agda
here, you can refer to the
[wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php) or the wonderful
[freenode channel](irc://chat.freenode.net/haskell).  While I go over all
concepts presented I won't go in depth to keep things reasonably brief.  This is
intended to get a taste of what Agda is capable of rather than explaining all
its features.  If you want to read document meant to be an introduction, you can
refer to the [many
tutorials](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Othertutorials)
available---personally I recommend Ulf Norell's 'Dependently Typed Programming
in Agda'.

## Agda lists

\begin{code}
module AgdaSort where
\end{code}

After the module declaration, let's warm up by defining a data type dear to
Haskell, a functional list:

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
bringing the type variables into scope manually.  In Agda, parameters in curly
braces are implicit and the type checker will try to infer them by unification.
This procedure can fail---type inference is undecidable---in which case the
implicits can be explicitly provided, also with curly braces.  Here we are also
omitting the type of the parameter `A` by using `∀`---we can do this since `A`
is an argument to `List` later in the signature.  For the converse reason we
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
= fst x , snd x` when deciding if two terms are equal.

## Unhabited types

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
*consistent*.  This has very pleasant consequences, the most prominent being
that all programs terminate.  For this reason consistent systems must be
Turing--incomplete (we can't write an infinite loops!), and thus Agda lets us
'step out' of these checks if we want to, although it is rarely needed---most
algorithms we write are quite easily provably terminating.  Note that
consistency wasn't put in Agda only to please mathematicians: given the
expressivity of the type system type checking and evaluation are tightly
intertwined, and thus we can send the compiler in an infinite loop if we can
write one.

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

For example we would expect terms of type `¬ (3 > 4)` to exist.  Here it starts
being clear that types are very 'first class' in Agda---functions can work on
them as they do with ordinary values: in this case `¬` takes a type and forms
another one.

## Different `Rel`ations

We need one last ingredient before we can start sorting.  We *could* write our
sort for some specific data type, say integers, but why would we do that
considering that we have a language that lets us express abstract structures
very naturally?

First we give a definition for a binary relation on a type `X`:

\begin{code}
Rel : Set → Set₁
Rel X = X → X → Set
\end{code}

The `Set₁` indicates that a relation between two `Set`s is 'larger' than a `Set`
itself---this is nothing to worry about now, but it follows a tradition in set
theory that goes back to Russell to avoid paradoxes [^girards].  `Set` is in
fact a shorthand for `Set₀` and represent the type of types of values: `Empty :
Set₀ : Set₁ : Set₂ : ...`.

[^girards]: In type theory this is known as Girards' paradox, you can find an
Agda (with `Set : Set` enabled) rendition
[here](http://code.haskell.org/Agda/test/succeed/Hurkens.agda).

Then we define the type of decidable relations---we would expect relations like
'less than' on integers or 'sortedness' on lists to be decidable:

\begin{code}
Decidable : ∀ {X} → Rel X → Set
Decidable R = ∀ x y → Either (R x y) (¬ (R x y))
\end{code}

That is, a decidable relation has a function that tells us if `x` and `y` are
related or not.

Now the interesting part.  To sort a list, we need two relations on the elements
of the list: some notion of equality and some ordering on the elements (in fact
the latter requires the former).  More formally, the equality will be an
[equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation):

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

Records are often used to collect abstract properties over types, much like type
classes are used in Haskell---only more flexible but without the big advantage
of having automatic instance resolution.

## Sorting

We can finally begin to sort.  To do this we will define a module parametrised
over a type and an ordering.  Agda has a very flexible module system---in fact
we have already been using it by defining records, which are implicitly modules.

\begin{code}
module Sort {X : Set} {_≈_ _≤_ : Rel X}
            (_≈?_ : Decidable _≈_) (_≤?_ : Decidable _≤_)
            (ord : TotalOrder _≈_ _≤_) where
  open TotalOrder ord using (trans; total; reflexive; equivalence)
  open Equivalence equivalence using (refl)
\end{code}

We require both relations to be decidable, and we bring in scope some fields of
the records using `open`, so that we can use them directly.

### Insertion sort

We want to represent bounded lists, but we want the bounds to be possibly
'open'.  For this purpose we wrap our type `X` in a data type that contains a
'top' and 'bottom' elements, that are respectively greater or equal and lower or
equal than all the other elements.

\begin{code}
  data ⊥X⊤ : Set where
    ⊤ ⊥ : ⊥X⊤
    ⟦_⟧ : X → ⊥X⊤
\end{code}

For `⊥X⊤` to be useful, we lift our ordering to work with it, following our
consideration for the top and bottom elements of `⊥X⊤`:

\begin{code}
  data _≤̂_ : ⊥X⊤ → ⊥X⊤ → Set where
    ⊥≤̂ : ∀ {x} → ⊥ ≤̂ x
    ≤̂⊤ : ∀ {x} → x ≤̂ ⊤
    x≤̂y : ∀ {x y} → x ≤ y → ⟦ x ⟧ ≤̂ ⟦ y ⟧
\end{code}

Note that this data type is different from what we have defined before: the
parameters to the type constructor can vary between data constructors---much
like in GADTs in Haskell.  In Agda, 'changing' parameters are known as
*indices*, as opposed to non--changing *parameters*.  Parameters are named and
to the left of the colon, while the type to the right of the colon will
determine the number and type of indices---in this case two `⊥X⊤`s.  This kind
of data type is known as an *inductive family*.

A 'sandwiching' relation will also be handy:

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
It's clear from how `cons` work that the elements in `OList` will be ordered
according to the `≤` relation.

We can easily get a 'normal' list back from an `OList`:

\begin{code}
  toList : ∀ {l u} → OList l u → List X
  toList (nil _) = []
  toList (cons x xs _) = x ∷ toList xs
\end{code}

With the right data types, writing and proving correct [^sortcorrect] an
[insertion sort](https://en.wikipedia.org/wiki/Insertion_sort) is a breeze---I
encourage you to try and writing yourself checking the goals as you pattern
match, the only non--trivial case being the last one:

[^sortcorrect]: Some might complain that actually we are only proving half of
the story, since we need to guarantee that the result list is a permutation of
the input list to prove a sorting algorithm correct.  That is doable but a bit
more involved.  What is very easy is to prove that length is preserved, see
[this file](https://github.com/bitonic/agda-examples/blob/master/Sort.agda) for
a version of this article which does exactly that.

\begin{code}
  insert : ∀ {l u} → (x : X) (xs : OList l u) → l ≤ x ≤ u → OList l u
  insert y (nil _)                 (l≤y , y≤u) = cons y (nil y≤u) (l≤y , y≤u)
  insert y (cons x xs (l≤x , x≤u)) _           with y ≤? x
  insert y (cons x xs (l≤x , x≤u)) (l≤y , y≤u) | left  y≤x =
    cons y (cons x xs (x≤̂y y≤x , x≤u)) (l≤y , y≤u)
  insert y (cons x xs (l≤x , x≤u)) (l≤y , y≤u) | right y>x =
    cons x (insert x xs (x≤̂y (reflexive refl) , x≤u)) (l≤x , x≤u)
\end{code}

Insertion sort is just a fold, where we use the type `OList ⊥ ⊤` to represent a
sorted list with 'open' bounds:

\begin{code}
  isort′ : List X → OList ⊥ ⊤
  isort′ = foldr (λ x xs → insert x xs (⊥≤̂ , ≤̂⊤)) (nil ⊥≤̂)

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
  newLeaf : ∀ {l u} → (x : X) → Tree l u → l ≤ x ≤ u → Tree l u
  newLeaf x (leaf _)       (l≤x , x≤u) = node x (leaf l≤x) (leaf x≤u)
  newLeaf x (node y ly yu) _           with x ≤? y
  newLeaf x (node y ly yu) (l≤x , x≤u) | left x≤y =
    node y (newLeaf x ly (l≤x , x≤̂y x≤y)) yu
  newLeaf x (node y ly yu) (l≤x , x≤u) | right x>y  =
    node y ly (newLeaf x yu ([ (λ x≤y → absurd (x>y x≤y)) , x≤̂y ] (total x y) , x≤u))
\end{code}

Again, the only tricky bit is the last one, where we need to convince Agda that
`y ≤ x` given that `¬ (x ≤ y)`.

Similar to `isort′`, turning a `List` into a `Tree` is a simple fold:

\begin{code}
  fromList : List X → Tree ⊥ ⊤
  fromList = foldr (λ x xs → newLeaf x xs (⊥≤̂ , ≤̂⊤)) (leaf ⊥≤̂)
\end{code}

Now we need to 'flatten' a `Tree` into an `OList`.  To do that we need a few
additional lemmas---first, transitivity for the lifted ordering:

\begin{code}
  ≤̂-trans : ∀ {l x u} → l ≤̂ x → x ≤̂ u → l ≤̂ u
  ≤̂-trans ⊥≤̂        _         = ⊥≤̂
  ≤̂-trans _         ≤̂⊤        = ≤̂⊤
  ≤̂-trans (x≤̂y l≤x) (x≤̂y x≤u) = x≤̂y (trans l≤x x≤u)
\end{code}

Here we use pattern matching in a new way: since the value of the indices of `≤̂`
depends on the constructors, matching on a constructor refines the context with
the new information.  For example in the first case pattern matching `⊥≤̂` turns
all occurrences of `l` into `⊥` in the respective context.  Pattern matching is
a much more powerful notion in Agda that is in in most (even dependently typed)
programming languages---it can not only change the context, but it will also
constraint the possible constructors of other parameters, if they are of a type
with indices and those indices have been refined.  This collection of techniques
are known as 'dependent pattern matching'.

Then, something that shows that the bounds of an ordered list are ordered
correctly:

\begin{code}
  OList-≤ : ∀ {l u} → OList l u → l ≤̂ u
  OList-≤ (nil l≤u)               = l≤u
  OList-≤ (cons x xu (l≤x , x≤u)) = ≤̂-trans l≤x (OList-≤ xu)
\end{code}

Now we can define `OList` concatenation, with the twist of inserting a new
element in the middle; and finally `flatten`:

\begin{code}
  _⇒_++_ : ∀ {l u} → (x : X) → OList l ⟦ x ⟧ → OList ⟦ x ⟧ u → OList l u
  x ⇒ nil l≤u               ++ xu = cons x xu (l≤u , OList-≤ xu)
  x ⇒ cons y yx (l≤y , y≤x) ++ xu =
    cons y (x ⇒ yx ++ xu) (l≤y , ≤̂-trans y≤x (OList-≤ xu))

  flatten : ∀ {l u} → Tree l u → OList l u
  flatten (leaf l≤u)     = (nil l≤u)
  flatten (node x lx xu) =  x ⇒ flatten lx ++ flatten xu
\end{code}

Then we are good with yet another fold.

\begin{code}
  treeSort′ : List X → OList ⊥ ⊤
  treeSort′ xs = flatten (foldr (λ x xs → newLeaf x xs (⊥≤̂ , ≤̂⊤)) (leaf ⊥≤̂) xs)

  treeSort : List X → List X
  treeSort xs = toList (treeSort′ xs)
\end{code}

## Propositional equality

Now lets put our module to work.  We will need a type equipped with the
appropriate relations, in this post I am going to use natural numbers.

For what concerns equality, we can actually define an inductive family that
relates equal terms:

\begin{code}
module PropositionalEquality where
  data _≡_ {X : Set} : Rel X where
    refl : ∀ {x} → x ≡ x
\end{code}

It's worth mentioned what 'equal' means here.  I have mentioned earlier that
'evaluation and typechecking are intertwined': when the type checker has to
decide if two types, or more generally two terms, are 'the same', it simply
reduces them as far as possible (to their 'normal form') and then compares them
syntactically.  Remember, every Agda term is terminating, so this procedure
itself is guaranteed to terminate.  Thus, `refl : ((λ x → x) 1) ≡ 1` is
acceptable, and so on.

This notion of equality is often called 'definitional' equality, as opposed to
the user--level equality expressed by the inductive family we have just defined,
which takes the name of 'propositional equality'.  Note that propositional
equality *does not* imply definitional equality, unless the prop. equality is a
closed term.  In the general case we might have prop. equalities in scope that
do not necessarily hold or involve abstracted variables, think of `λ (p : 3 ≡ 1)
→ ...`.

Let's prove that `≡` is an equivalent relation, and a `cong`ruence law which
will be useful later:

\begin{code}
  sym : ∀ {X} {x y : X} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {X} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  equivalence : ∀ {X} → Equivalence {X} _≡_
  equivalence = record { refl = refl; sym = sym; trans = trans }

  cong : ∀ {X} {x y : X} → (f : X → X) → x ≡ y → f x ≡ f y
  cong _ refl = refl
\end{code}

All the definitions above rely on the dependent pattern matching mentioned
before.

## Natural numbers

\begin{code}
module Nat where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ    #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}
\end{code}

The definition for naturals is the usual one---the pragmas are there so that we
can use number literals.

Then we define a procedure to decide equality for naturals:

\begin{code}
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
\end{code}

\begin{code}
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
