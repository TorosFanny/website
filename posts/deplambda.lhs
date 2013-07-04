---
title: Simply easy
date: 2013-07-03
published: false
---

TODO fixities

> {-# LANGUAGE DeriveFoldable #-}
> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE OverloadedStrings #-}
> {-# LANGUAGE TypeSynonymInstances #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}
> {-# OPTIONS_GHC -fno-warn-orphans #-}
> import Control.Applicative (Applicative(..), (<$>), (<$))
> import Control.Arrow (first)
> import Control.Monad (liftM, ap, unless)
> import Control.Monad.State
>     (StateT, runStateT, State, evalState, get, gets, put, lift)
> import Data.Foldable (Foldable, msum)
> import Data.Map (Map)
> import Data.Maybe (fromMaybe)
> import Data.String (IsString(..))
> import Data.Traversable (Traversable, traverse)
> import Text.PrettyPrint.Leijen (Pretty(..), Doc, (<+>), (<>))
> import qualified Data.Map as Map
> import qualified Text.PrettyPrint.Leijen as PP

Term representation
----

> type Id = String
> newtype Name = Name Id
>     deriving (Show)
> instance Eq  Name where _ == _ = True
> instance Ord Name where compare _ _ = EQ

> data Var v = Bound Name | Free v
>     deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
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
>
>     | Tm v :∈ Ty v            -- Annotated type
>     deriving (Eq, Show, Functor, Foldable, Traversable)
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
>     t :∈ ty      >>= f = (t  >>= f) :∈ (ty >>= f)
>
> (>>>=) :: (Monad m) => Scope m a -> (a -> m b) -> Scope m b
> s >>>= f = s >>= bump
>   where bump (Bound n) = return (Bound n)
>         bump (Free v)  = Free `liftM` f v

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

> lam :: Id -> Tm Id -> Tm Id
> lam n t = Lam (abstract n t)
>
> arr, prod :: Id -> Ty Id -> Ty Id -> Ty Id
> arr  n ty₁ ty₂ = ty₁ :→ abstract n ty₂
> prod n ty₁ ty₂ = ty₁ :* abstract n ty₂

Parsing
----

Pretty printing
----

> class HasName a where
>     name :: a -> Id
> instance HasName Id where
>     name = id
> instance HasName v => HasName (Var v) where
>     name (Free v)         = name v
>     name (Bound (Name n)) = n

> type Count = Int
> nameCount :: Id -> Count -> Id
> nameCount n c = n ++ if c == 0 then "" else show c

> slam :: (Ord v, HasName v) => Tm v -> Tm Id
> slam t = evalState (traverse fresh t)
>                    (Map.empty :: Map v Count, Map.empty :: Map Id Count)
>   where
>     fresh v =
>         do vcount <- gets fst
>            c <- maybe (newCount v) return (Map.lookup v vcount)
>            return (nameCount (name v) c)
>
>     newCount v =
>         do (vcount, idcount) <- get
>            let n = name v
>                c = fromMaybe 0 (Map.lookup n idcount)
>            c <$ put (Map.insert v c vcount, Map.insert n (c + 1) idcount)

>
> type PPM = State (Map Id Count)
>
> boundName :: (Foldable m, Monad m) => Scope m Id -> PPM (Maybe Id, m Id)
> boundName t =
>     case msum (f `liftM` t) of
>         Nothing -> return (Nothing, t @@ undefined)
>         Just n  -> do idcount <- get
>                       let c  = fromMaybe 0 (Map.lookup n idcount)
>                           n' = nameCount n c
>                       (Just n', t @@ return n') <$ put (Map.insert n c idcount)
>   where
>     f (Bound (Name n)) = Just n
>     f (Free _)         = Nothing
>
> boundName' :: (Foldable m, Monad m) => Scope m Id -> PPM (Id, m Id)
> boundName' s = first (fromMaybe "_") <$> boundName s
>
> instance IsString Doc where
>     fromString = PP.text
>
> ppPretty :: Tm Id -> PPM Doc
> ppPretty Ty             = return "*"
> ppPretty (Var v)        = return (PP.text (name v))
> ppPretty Unit           = return "Unit"
> ppPretty Tt             = return "tt"
> ppPretty Empty          = return "Empty"
> ppPretty (Absurd t)     = fmap ("absurd" <+>) (ppParens t)
> ppPretty t@(_ :→ _)     = ppArr t
> ppPretty t@(Lam _)      = ppLam t
> ppPretty t@(_ :@ _)     = ppApps t
> ppPretty (fsty :* snty) = ppBinder "->" ppApps fsty snty
> ppPretty (Pair fs ty)   = middle ", " (ppApps fs) (ppApps ty)
> ppPretty (Fst t)        = fmap ("fst" <+>) (ppParens t)
> ppPretty (Snd t)        = fmap ("snd" <+>) (ppParens t)
> ppPretty (t :∈ ty)      = ppTyped t ty
>
> compound :: Tm v -> Bool
> compound Ty      = False
> compound (Var _) = False
> compound Unit    = False
> compound Tt      = False
> compound Empty   = False
> compound _       = True
>
> ppParens :: Tm Id -> PPM Doc
> ppParens t = if compound t then PP.parens <$> ppPretty t else ppPretty t
>
> ppArr :: Tm Id -> PPM Doc
> ppArr (dom :→ cod) = ppBinder "->" ppArr dom cod
> ppArr t            = ppApps t
>
> ppLam :: Tm Id -> PPM Doc
> ppLam t₀ = fmap ("\\" <>) (go t₀)
>   where
>     go (Lam s) = do (arg, t) <- boundName' s; fmap (PP.text arg <+>) (go t)
>     go t       = fmap ("=>" <+>) (ppApps t)
>
> ppApps :: Tm Id -> PPM Doc
> ppApps (t₁ :@ t₂) = (<+>) <$> ppApps t₁ <*> ppParens t₂
> ppApps t          = ppParens t
>
> middle :: String -> PPM Doc -> PPM Doc -> PPM Doc
> middle s x₁ x₂ =
>     do doc₁ <- x₁
>        doc₂ <- x₂
>        return (doc₁ <> PP.text s <> doc₂)
>
> ppBinder :: String -> (Tm Id -> PPM Doc) -> Tm Id -> Scope Tm Id -> PPM Doc
> ppBinder tok pp ty₁ ty₂ =
>     do ty₁doc      <- ppApps ty₁
>        (arg, ty₂') <- boundName ty₂
>        ty₂doc      <- pp ty₂'
>        return (case arg of
>                    Nothing -> ty₁doc
>                    Just n  -> "[" <> PP.text n <+> ":" <+> ty₁doc <> "]"
>                <+> PP.text tok <+> ty₂doc)
>
> ppTyped :: Tm Id -> Ty Id -> PPM Doc
> ppTyped t₁ t₂ = middle " : " (ppApps t₁) (ppApps t₂)
>
> instance (Ord v, HasName v) => Pretty (Tm v) where
>      pretty t = evalState (ppPretty (slam t)) Map.empty

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

> type Ctx v m = v -> Maybe (m v)
> type Tys v = Ctx v Ty
> type Defs v = Ctx v Tm
>
> ε :: Ctx v m
> ε = const Nothing
>
> insert :: (Eq v) => v -> m v -> Ctx v m -> Ctx v m
> insert v x ctx v' = if v == v' then Just x else ctx v'
>
> (◁◁) :: Functor m => Ctx v m -> Maybe (m v) -> Ctx (Var v) m
> (_   ◁◁ t) (Bound _) = fmap Free <$> t
> (ctx ◁◁ _) (Free v)  = fmap Free <$> ctx v
>
> (◁) :: Functor m => Ctx v m -> m v -> Ctx (Var v) m
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
>   do tys <- gets snd
>      maybe (tyError (OutOfBounds (name v))) return (tys v)
>
> nf :: HasName v => Tm v -> TCM v (Tm v)
> nf t = (⇓ t) <$> gets fst

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
