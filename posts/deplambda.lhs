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
> import Control.Monad (ap, unless)
> import Control.Monad.State (StateT, get, gets, runStateT, lift)

> type Id = String
> newtype Name = Name Id
>     deriving (Show)
> instance Eq  Name where _ == _ = True

> data Var v = Bound Name | Free v
>     deriving (Eq, Show, Functor)
>
> bound :: Id -> Var Id
> bound = Bound . Name

> type Scope m v = m (Var v)
> data Tm v
>     = Ty
>     | Var v
>     | Tm v :@ Tm v
>     | Lam (Scope Tm v)
>     | Ty v :-> Scope Ty v
>     | Tm v :∈ Ty v
>     deriving (Eq, Show, Functor)
> type Ty = Tm

> instance Applicative Tm where
>     pure  = return
>     (<*>) = ap
>
> instance Monad Tm where
>     return = Var
>
>     Ty          >>= _ = Ty
>     Var v       >>= f = f v
>     t₁ :@ t₂    >>= f = (t₁ >>= f) :@ (t₂ >>= f)
>     t  :∈ ty    >>= f = (t  >>= f) :∈ (ty >>= f)
>     Lam s       >>= f = Lam (s >>>= f)
>     ty₁ :-> ty₂ >>= f = (ty₁ >>= f) :-> (ty₂ >>>= f)
>
> (>>>=) :: (Monad m) => Scope m a -> (a -> m b) -> Scope m b
> s >>>= f = s >>= bump
>   where bump (Bound n) = return (Bound n)
>         bump (Free v)  = f v >>= return . Free

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

> type Ctx m v = v -> m v
> type Tys v = Ctx Ty v
> newtype Def v = Def {unDefs :: Maybe (Tm v)} deriving (Functor)
> type Defs v = Ctx Def v
>
> (◁) :: Functor m => Ctx m v -> m v -> Ctx m (Var v)
> (ctx ◁ t) (Bound _) = Free <$> t
> (ctx ◁ t) (Free v)  = Free <$> ctx v
>
> nestDefs :: Defs v -> Defs (Var v)
> nestDefs defs = defs ◁ Def Nothing

> (⇓) :: Defs v -> Tm v -> Tm v
> _   ⇓ Ty            = Ty
> defs ⇓ Var v         = maybe (Var v) (defs ⇓) (unDefs (defs v))
> defs ⇓ (t₁ :@ t₂)    = (defs ⇓ t₁) :@ (defs ⇓ t₂)
> defs ⇓ (t  :∈ ty)    = (defs ⇓ t ) :∈ (defs ⇓ ty)
> defs ⇓ Lam s         = Lam (nestDefs defs ⇓ s)
> defs ⇓ (ty₁ :-> ty₂) = (defs ⇓ ty₁) :-> (nestDefs defs ⇓ ty₂)

> class HasName a where
>     name :: a -> Id
> instance HasName Id where
>     name = id
> instance HasName v => HasName (Var v) where
>     name (Free v)         = name v
>     name (Bound (Name n)) = n
>
> data TyError
>     = OutOfBounds Id
>     | TyError String
>     | ExpectingFunction       -- TODO better
>     | Mismatch                -- TODO better
>
> type TCM v = StateT (Defs v, Tys v) (Either TyError)
>
> tyError :: TyError -> TCM v a
> tyError = lift . Left
>
> getDefs :: TCM v (Defs v)
> getDefs = gets fst
> getTys :: TCM v (Tys v)
> getTys = gets snd
>
> nest :: Ty v -> TCM (Var v) a -> TCM v a
> nest ty m =
>     do (defs, tys) <- get
>        case runStateT m (nestDefs defs, tys ◁ ty) of
>            Left err     -> tyError err
>            Right (x, _) -> return x
>
> nf :: HasName v => Tm v -> TCM v (Tm v)
> nf t = (⇓ t) <$> getDefs
>
> infer :: (Eq v, HasName v) => Tm v -> TCM v (Ty v)
> infer Ty = return Ty
> infer (Var v) = getTys <*> return v
> infer (t₁ :@ t₂) =
>     do ty₁ <- inferNf t₁
>        case ty₁ of
>            dom :-> cod -> (cod @@ dom) <$ (t₂ ∈ dom)
>            _           -> tyError ExpectingFunction
>
> inferNf :: (Eq v, HasName v) => Tm v -> TCM v (Ty v)
> inferNf t = nf =<< infer t
>
> (∈) :: (Eq v, HasName v) => Tm v -> Ty v -> TCM v ()
> t₀ ∈ ty₀ = (`check` ty₀) =<< nf t₀
>   where
>     check :: (Eq v, HasName v) => Tm v -> Ty v -> TCM v ()
>     check (Lam s) (dom :-> cod) = nest dom (check s cod)
>     check t ty =
>       do tyt <- inferNf t
>          unless (ty == tyt) (tyError Mismatch)

> main :: IO ()
> main = undefined
