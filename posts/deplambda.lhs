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
> {-# LANGUAGE OverloadedStrings #-}
> {-# LANGUAGE TupleSections #-}
> {-# LANGUAGE TypeSynonymInstances #-}
> import Control.Applicative (Applicative(..), (<$>), (<$), (<|>))
> import Control.Arrow (first)
> import Control.Monad (liftM, ap, unless, void)
> import Control.Monad.State
>     (StateT, runStateT, State, evalState, get, gets, put, modify, lift)
> import Data.Foldable (Foldable, msum)
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe (fromMaybe)
> import Data.Traversable (Traversable, traverse)
> import Text.Parsec ((<?>), ParseError)
> import qualified Text.Parsec as P
> import Text.Parsec.String
> import Text.PrettyPrint (Doc, (<+>), (<>), ($$), ($+$))
> import qualified Text.PrettyPrint as PP
> import System.Console.Haskeline
>     (InputT, getInputLine, runInputT, defaultSettings)
> import System.Console.Haskeline.MonadException ()


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

> infixl 3 <||>
> (<||>) :: Parser a -> Parser a -> Parser a
> p₁ <||> p₂ = P.try p₁ <|> p₂
>
> lexeme :: String -> Parser ()
> lexeme s = void (P.string s <* P.spaces)

> pTm :: Parser (Tm Id)
> pTm = pCompound
>
> pSingle :: Parser (Tm Id)
> pSingle =
>          Ty    <$  lexeme "Ty"
>     <||> Var   <$> pId
>     <||> Unit  <$  lexeme "Unit"
>     <||> Tt    <$  lexeme "tt"
>     <||> Empty <$  lexeme "Empty"
>     <?>  "single term"
>
> pCompound :: Parser (Tm Id)
> pCompound =
>          Absurd <$> (lexeme "absurd" *> pParens)
>     <||> pArr
>     <||> pLam
>     <||> pBinder "*" prod pApp
>     <||> Pair <$> pParens <*> (lexeme "," *> pParens)
>     <||> Fst <$> (lexeme "fst" *> pParens)
>     <||> Snd <$> (lexeme "snd" *> pParens)
>     <||> uncurry (:∈) <$> pTyped pApp
>     <||> pApp
>     <?>  "compound term"
>
> pId :: Parser Id
> pId = (((:) <$> P.alphaNum <*> P.many idp) <* P.spaces) <?> "identifier"
>   where idp = P.alphaNum <||> P.digit <||> P.oneOf "_-'"
>
> pParens :: Parser (Tm Id)
> pParens = pSingle <||> (lexeme "(" *> pCompound <* lexeme ")")
>
> pArr :: Parser (Tm Id)
> pArr = bi (bi pApp <||> pApp) where bi = pBinder "->" arr
>
> pLam :: Parser (Tm Id)
> pLam = P.string "\\" *> go
>   where go = lexeme "=>" *> pApp <||>
>              lam <$> (P.string "_" <||> pId) <*> go
>
> pApp :: Parser (Tm Id)
> pApp = foldl1 (:@) <$> P.many1 pParens
>
> pBinder :: String -> (Id -> Ty Id -> Ty Id -> Ty Id) -> Parser (Ty Id)
>         -> Parser (Ty Id)
> pBinder tok f p = dep <||> simple
>   where
>     dep = do lexeme "["
>              (v, ty₁) <- pTyped pId
>              lexeme "]"
>              lexeme tok
>              f v ty₁ <$> p
>     simple = f "_" <$> pApp <*> (lexeme tok *> pApp)
>
> pTyped :: Parser a -> Parser (a, Ty Id)
> pTyped p = (,) <$> p <*> (lexeme ":" *> pApp)

Pretty printing
----

> class Ord a => Slam a where
>     name :: a -> Id
> instance Slam Id where
>     name = id
> instance Slam v => Slam (Var v) where
>     name (Free v)         = name v
>     name (Bound (Name n)) = n

> type Count = Int
> nameCount :: Id -> Count -> Id
> nameCount n c = n ++ if c == 0 then "" else show c

> slam :: (Slam v) => Tm v -> Tm Id
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
> ppTm :: (Slam v) => Tm v -> Doc
> ppTm t = evalState (ppTm' (slam t)) Map.empty
>
> ppTm' :: Tm Id -> PPM Doc
> ppTm' Ty             = return "Ty"
> ppTm' (Var v)        = return (PP.text (name v))
> ppTm' Unit           = return "Unit"
> ppTm' Tt             = return "tt"
> ppTm' Empty          = return "Empty"
> ppTm' (Absurd t)     = fmap ("absurd" <+>) (ppParens t)
> ppTm' t@(_ :→ _)     = ppArr t
> ppTm' t@(Lam _)      = ppLam t
> ppTm' t@(_ :@ _)     = ppApps t
> ppTm' (fsty :* snty) = ppBinder "->" ppApps fsty snty
> ppTm' (Pair fs ty)   = middle ", " (ppApps fs) (ppApps ty)
> ppTm' (Fst t)        = fmap ("fst" <+>) (ppParens t)
> ppTm' (Snd t)        = fmap ("snd" <+>) (ppParens t)
> ppTm' (t :∈ ty)      = ppTyped t ty
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
> ppParens t = if compound t then PP.parens <$> ppTm' t else ppTm' t
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


Reduction
----

> nf :: Tm v -> Tm v
> nf Ty             = Ty
> nf t@(Var _)      = t
> nf Unit           = Unit
> nf Tt             = Tt
> nf Empty          = Empty
> nf (Absurd t)     = Absurd (nf t)
> nf (dom :→ cod)   = nf dom :→ nf cod
> nf (Lam s)        = Lam (nf s)
> nf (t₁ :@ t₂)     = nf t₁ :@ nf t₂
> nf (tyfs :* tysn) = nf tyfs :* nf tysn
> nf (Pair fs sn)   = Pair (nf fs) (nf sn)
> nf (Fst t)        = case nf t of
>                         Pair fs _ -> fs
>                         t'        -> t'
> nf (Snd t)        = case nf t of
>                         Pair _ sn -> sn
>                         t'        -> t'
> nf (t :∈ ty)      = nf t :∈ nf ty

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
>
> ε :: Ctx v m
> ε = const Nothing
>
> insert :: (Eq v) => v -> m v -> Ctx v m -> Ctx v m
> insert v x ctx v' = if v == v' then Just x else ctx v'
>
> (◁) :: (Functor m) => Ctx v m -> m v -> Ctx (Var v) m
> (_   ◁ t) (Bound _) = Just (Free <$> t)
> (ctx ◁ _) (Free v)  = fmap Free <$> ctx v

Type checking
----

> data TyError
>     = OutOfBounds Id
>     | ExpectingFun (Tm Id) (Ty Id)
>     | ExpectingProd (Tm Id) (Ty Id)
>     | Mismatch (Ty Id) (Tm Id) (Ty Id)
>     | NotAnnotated (Tm Id)
>     | ParseError ParseError
>
> expectingFun :: (Slam v) => Tm v -> Tm v -> TCM v a
> expectingFun t ty = tyError (ExpectingFun (slam t) (slam ty))
> expectingProd :: (Slam v) => Tm v -> Tm v -> TCM v a
> expectingProd t ty = tyError (ExpectingProd (slam t) (slam ty))
>
> nest4 :: Doc -> Doc
> nest4 = PP.nest 4
>
> ppError :: TyError -> Doc
> ppError (OutOfBounds n) = "Out of bound variable" <+> ppQuote (PP.text n)
> ppError (ExpectingFun t ty) =
>     "Expecting function type for term:" $$ nest4 (ppTm t) $$
>     "instead of:" $$ nest4 (ppTm ty)
> ppError (ExpectingProd t ty) =
>     "Expecting product type for term:" $$ nest4 (ppTm t) $$
>     "instead of:" $$ nest4 (ppTm ty)
> ppError (Mismatch ty t tyt) =
>     "Expecting type:" $$ nest4 (ppTm ty) $$
>     "for term:" $$ nest4 (ppTm t) $$
>     "instead of:" $$ nest4 (ppTm tyt)
> ppError (NotAnnotated t) =
>     "Unannotated canonical term:" $$ nest4 (ppTm t)
> ppError (ParseError err) = PP.text (show err)

> ppQuote :: Doc -> Doc
> ppQuote d = "`" <> d <> "'"
>
> type Tys v = Ctx v Ty
> type TCM v = StateT (Tys v) (Either TyError)
>
> tyError :: TyError -> TCM v a
> tyError = lift . Left
>
> lookupTy :: (Slam v) => v -> TCM v (Ty v)
> lookupTy v =
>   do tys <- get
>      maybe (tyError (OutOfBounds (name v))) return (tys v)

> nest :: Ty v -> TCM (Var v) a -> TCM v a
> nest ty m =
>     do tys <- get
>        case runStateT m (tys ◁ ty) of
>            Left err     -> tyError err
>            Right (x, _) -> return x
>
> infer :: (Slam v) => Tm v -> TCM v (Ty v)
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
>            _          -> expectingFun t₁ ty₁
> infer (tyfs :* tysn) = inferBind tyfs tysn
> infer (Fst t) =
>     do ty <- inferNf t
>        case ty of
>            tyfs :* _ -> return tyfs
>            _         -> expectingProd t ty
> infer (Snd t) =
>     do let t' = nf t
>        ty <- inferNf t'
>        case (t', ty) of
>            (Pair fs _, _ :* tysn) -> return (tysn @@ fs)
>            _                      -> expectingProd t ty
> infer (t :∈ ty) = ty <$ t ∈ ty
> infer t = tyError (NotAnnotated (slam t))
>
> inferNf :: (Slam v) => Tm v -> TCM v (Ty v)
> inferNf t = nf <$> infer t
>
> inferBind :: (Slam v) => Tm v -> Tm (Var v) -> TCM v (Tm v)
> inferBind ty s = do ty ∈ Ty; nest ty (s ∈ Ty); return Ty
>
> (∈) :: (Slam v) => Tm v -> Ty v -> TCM v ()
> t₀ ∈ ty₀ = check (nf t₀) ty₀
>   where
>     check :: (Slam v) => Tm v -> Ty v -> TCM v ()
>     check (Absurd t) _ = check t Empty
>     check (Lam s) (dom :→ cod) = nest dom (check s cod)
>     check t@(Lam _) ty = expectingFun t ty
>     check (Pair fs sn) (tyfs :* tysn) =
>         do check fs tyfs; check sn (tysn @@ fs)
>     check t@(Pair _ _) ty = expectingProd t ty
>     check t ty =
>         do tyt <- inferNf t
>            unless (ty == tyt) (tyError (Mismatch (slam ty) (slam t) (slam tyt)))

A REPL
----

> data Def = Def Id (Ty Id) (Maybe (Tm Id))
> type Defs = Map Id (Tm Id)
>
> pDef :: Parser Def
> pDef = post <||> body
>   where
>     post =
>         do lexeme "postulate"
>            (v, ty) <- pTyped pId
>            return (Def v ty Nothing)
>     body =
>         do lexeme "let"
>            (v, ty) <- pTyped pId
>            lexeme "=>"
>            t <- pTm
>            return (Def v ty (Just t))

> data Input
>     = IInfer (Tm Id)
>     | IEval (Tm Id)
>     | IDef Def
>     | IQuit
>     | ISkip

> data Output
>     = OInfer (Ty Id)
>     | OEval (Tm Id) (Ty Id)
>     | OQuit
>     | OOK
>     | OSkip
>
> ppOutput :: Output -> Doc
> ppOutput (OInfer ty)  = "Type:" $$ nest4 (ppTm ty)
> ppOutput (OEval t ty) = ppOutput (OInfer ty) $+$ ppTm t
> ppOutput OQuit        = ""
> ppOutput OOK          = "OK"
> ppOutput OSkip        = ""

> pInput :: Parser Input
> pInput =
>          (command <?> "command")
>     <||> ((IDef <$> pDef) <?> "definition")
>     <||> IEval <$> pTm
>     <||> return ISkip
>   where
>     command  = P.char ':' *> msum [P.char ch *> p | (ch, p) <- commands]
>     commands = [('t', IInfer <$> pTm), ('q', return IQuit)]
>
> input :: String -> TCM Id Input
> input =
>     either (tyError . ParseError) return .
>     P.parse (P.spaces *> pInput <* P.spaces <* P.eof) ""

> newDef :: Def -> Defs -> TCM Id Defs
> newDef (Def n ty₀ tm₀) defs =
>     do ty ∈ Ty
>        defs' <- case tm of
>                     Nothing -> return defs
>                     Just t  -> do t  ∈ ty; return (Map.insert n t defs)
>        modify (insert n ty)
>        return defs'
>   where
>     untop t' = do v <- t'; fromMaybe (Var v) (Map.lookup v defs)
>     tm = untop <$> tm₀
>     ty = untop ty₀

> repl :: String -> Defs -> TCM Id (Output, Defs)
> repl inps defs =
>     do inp <- input inps
>        case inp of
>            IInfer t -> (, defs) . OInfer <$> infer t
>            IEval t  -> (, defs) . OEval (nf t) <$> infer t
>            IDef def -> (OOK,) <$> newDef def defs
>            IQuit    -> return (OQuit, defs)
>            ISkip    -> return (OSkip, defs)

> run :: Tys Id -> Defs -> InputT IO ()
> run tys defs =
>     do sm <- getInputLine ">>> "
>        case sm of
>            Nothing -> run tys defs
>            Just s ->
>                case runStateT (repl s defs) tys of
>                    Left err ->
>                        do putDocLn (ppError err)
>                           run tys defs
>                    Right ((OQuit, _), _)   -> return ()
>                    Right ((out, defs'), tys') ->
>                        do putDocLn (ppOutput out)
>                           run tys' defs'
>   where putDocLn = lift . putStrLn . PP.render

> main :: IO ()
> main = runInputT defaultSettings (run ε Map.empty)
