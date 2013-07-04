---
title: Simply easy
date: 2013-07-03
published: false
---

TODO fixities

> {-# LANGUAGE TypeSynonymInstances #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE DeriveFunctor #-}
> import Control.Applicative (Applicative(..), (<$>), (<$))
> import Control.Monad (ap, unless, liftM)
> import Control.Monad.State (StateT, get, gets, runStateT, lift)

Term representation
----

> type Id = String
> newtype Name = Name Id
>     deriving (Show)
> instance Eq Name where _ == _ = True

> data Var v = Bound Name | Free v
>     deriving (Eq, Show, Functor)
>
> bound :: Id -> Var Id
> bound = Bound . Name

> type Scope m v = m (Var v)
> data Tm v
>     = Ty                      -- The type of types
>     | Var v                   -- A variable
>
>     | Unit                    -- Top, (), ...
>     | Tt                      -- Trivial inhabitant of Unit
>     | Empty                   -- Void
>     | Absurd (Tm v)           -- Ex falso quodlibet
>
>     | Ty v :→ Scope Ty v      -- Dependent arrow
>     | Lam (Scope Tm v)        -- Abstraction
>     | Tm v :@ Tm v            -- Application
>
>     | Ty v :* Scope Ty v      -- Dependent product
>     | Pair (Tm v) (Tm v)
>     | Fst (Tm v)
>     | Snd (Tm v)

>     | Tm v :∈ Ty v            -- Annotated type
>     deriving (Eq, Show, Functor)
> type Ty = Tm

> instance Applicative Tm where
>     pure  = return
>     (<*>) = ap
>
> instance Monad Tm where
>     return = Var
>
>     Ty           >>= _ = Ty
>     Var v        >>= f = f v
>     Unit         >>= _ = Unit
>     Tt           >>= _ = Tt
>     Empty        >>= _ = Empty
>     Absurd t     >>= f = Absurd (t >>= f)
>     dom :→ cod   >>= f = (dom >>= f) :→ (cod >>>= f)
>     Lam s        >>= f = Lam (s >>>= f)
>     t₁ :@ t₂     >>= f = (t₁ >>= f) :@ (t₂ >>= f)
>     tyfs :* tysn >>= f = (tyfs >>= f) :* (tysn >>>= f)
>     Pair t₁ t₂   >>= f = Pair (t₁ >>= f) (t₂ >>= f)
>     Fst t        >>= f = Fst (t >>= f)
>     Snd t        >>= f = Snd (t >>= f)
>     t  :∈ ty     >>= f = (t  >>= f) :∈ (ty >>= f)
>
> (>>>=) :: (Monad m) => Scope m a -> (a -> m b) -> Scope m b
> s >>>= f = s >>= bump
>   where bump (Bound n) = return (Bound n)
>         bump (Free v)  = Free `liftM` f v

> subst :: (Eq v, Monad m) => v -> m v -> m v -> m v
> subst v t₁ t₂ =
>     do v' <- t₂
>        if v == v' then t₂ else return v'
>
> (@@) :: (Monad m) => Scope m v -> m v -> m v
> s @@ t =
>     do v <- s
>        case v of
>            Bound _ -> t
>            Free v' -> return v'
>
> abstract :: (Monad m) => Id -> m Id -> Scope m Id
> abstract v t =
>     do v' <- t
>        return (if v == v' then bound v else Free v')

Parsing
----

Contexts
----

Blah blah.[^gadt]

[^gadt]:
< data Ctx m v where
<     C0   :: Ctx m v
<     (:◁) :: Ctx m v -> m v -> Ctx m (Var v)
<
< lookCtx :: Functor m => Ctx m v -> v -> Maybe (m v)
< lookCtx C0         _         = Nothing
< lookCtx (ctx :◁ _) (Free v)  = fmap Free <$> lookCtx ctx v
< lookCtx (_   :◁ t) (Bound _) = Just (Free <$> t)

> type Ctx m v = v -> Maybe (m v)
> type Tys v = Ctx Ty v
> type Defs v = Ctx Tm v
>
> (◁◁) :: Functor m => Ctx m v -> Maybe (m v) -> Ctx m (Var v)
> (ctx ◁◁ t) (Bound _) = fmap Free <$> t
> (ctx ◁◁ t) (Free v)  = fmap Free <$> ctx v
>
> (◁) :: Functor m => Ctx m v -> m v -> Ctx m (Var v)
> ctx ◁ t = ctx ◁◁ Just t

Reduction
----

> nestDefs :: Defs v -> Defs (Var v)
> nestDefs defs = defs ◁◁ Nothing

> (⇓) :: Defs v -> Tm v -> Tm v
> _    ⇓ Ty             = Ty
> defs ⇓ Var v          = maybe (Var v) (defs ⇓) (defs v)
> _    ⇓ Unit           = Unit
> _    ⇓ Tt             = Tt
> _    ⇓ Empty          = Empty
> defs ⇓ Absurd t       = Absurd (defs ⇓ t)
> defs ⇓ (dom :→ cod)   = (defs ⇓ dom) :→ (nestDefs defs ⇓ cod)
> defs ⇓ Lam s          = Lam (nestDefs defs ⇓ s)
> defs ⇓ (t₁ :@ t₂)     = (defs ⇓ t₁) :@ (defs ⇓ t₂)
> defs ⇓ (tyfs :* tysn) = (defs ⇓ tyfs) :* (nestDefs defs ⇓ tysn)
> defs ⇓ Pair fs sn     = Pair (defs ⇓ fs) (defs ⇓ sn)
> defs ⇓ Fst t          = case defs ⇓ t of
>                             Pair fs _ -> fs
>                             t'        -> t'
> defs ⇓ Snd t          = case defs ⇓ t of
>                             Pair _ sn -> sn
>                             t'        -> t'
> defs ⇓ (t :∈ ty)      = (defs ⇓ t ) :∈ (defs ⇓ ty)

A Monad
----

> data TyError
>     = OutOfBounds Id
>     | TyError String
>     | ExpectingFunction       -- TODO better
>     | ExpectingPair           -- TODO better
>     | Mismatch                -- TODO better
>     | NotAnnotated            -- TODO better
>
> type TCM v = StateT (Defs v, Tys v) (Either TyError)
>
> tyError :: TyError -> TCM v a
> tyError = lift . Left
>
> lookupTy :: (HasName v) => v -> TCM v (Ty v)
> lookupTy v =
>   gets snd <*> pure v >>=
>   maybe (tyError (OutOfBounds (name v))) return
>
> nf :: HasName v => Tm v -> TCM v (Tm v)
> nf t = (⇓ t) <$> gets fst

Pretty printing
----

> class HasName a where
>     name :: a -> Id
> instance HasName Id where
>     name = id
> instance HasName v => HasName (Var v) where
>     name (Free v)         = name v
>     name (Bound (Name n)) = n

Type checking
----

> nest :: Ty v -> TCM (Var v) a -> TCM v a
> nest ty m =
>     do (defs, tys) <- get
>        case runStateT m (nestDefs defs, tys ◁ ty) of
>            Left err     -> tyError err
>            Right (x, _) -> return x
>
> infer :: (Eq v, HasName v) => Tm v -> TCM v (Ty v)
> infer Ty = return Ty
> infer (Var v) = lookupTy v
> infer Unit = return Ty
> infer Tt = return Unit
> infer Empty = return Ty
> infer (dom :→ cod) = inferBind dom cod
> infer (t₁ :@ t₂) =
>     do ty₁ <- inferNf t₁
>        case ty₁ of
>            dom :→ cod -> (cod @@ dom) <$ (t₂ ∈ dom)
>            _          -> tyError ExpectingFunction
> infer (tyfs :* tysn) = inferBind tyfs tysn
> infer (Fst t) =
>     do ty <- inferNf t
>        case ty of
>            tyfs :* _ -> return tyfs
>            _         -> tyError ExpectingPair
> infer (Snd t) =
>     do t' <- nf t
>        ty <- inferNf t'
>        case (t', ty) of
>            (Pair fs _, _ :* tysn) -> return (tysn @@ fs)
>            _                      -> tyError ExpectingPair
> infer _ = tyError NotAnnotated
>
> inferNf :: (Eq v, HasName v) => Tm v -> TCM v (Ty v)
> inferNf t = nf =<< infer t
>
> inferBind :: (Eq v, HasName v) => Tm v -> Tm (Var v) -> TCM v (Tm v)
> inferBind ty s = do ty ∈ Ty; nest ty (s ∈ Ty); return Ty
>
> (∈) :: (Eq v, HasName v) => Tm v -> Ty v -> TCM v ()
> t₀ ∈ ty₀ = (`check` ty₀) =<< nf t₀
>   where
>     check :: (Eq v, HasName v) => Tm v -> Ty v -> TCM v ()
>     check (Absurd t) _ = check t Empty
>     check (Lam s) (dom :→ cod) = nest dom (check s cod)
>     check (Pair fs sn) (tyfs :* tysn) =
>         do check fs tyfs; check sn (tysn @@ fs)
>     check t ty =
>         do tyt <- inferNf t
>            unless (ty == tyt) (tyError Mismatch)

A REPL
----

> main :: IO ()
> main = undefined
