module LiterateAgda where


import Control.Monad.State
import Control.Monad.Error
import Control.Applicative

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Function
import Data.Monoid

import System.Environment
import System.Exit
import System.FilePath
import Text.XHtml.Strict

import Agda.Syntax.Position hiding (Range)
import Agda.Syntax.Parser
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Abstract.Name hiding (Name)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Common


import Agda.Interaction.Exceptions
import Agda.Interaction.CommandLine.CommandLine
import Agda.Interaction.Options
import Agda.Interaction.Monad
import Agda.Interaction.GhcTop (mimicGHCi)
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range
import qualified Agda.Interaction.Imports as Imp
import qualified Agda.Interaction.Highlighting.Dot as Dot
import qualified Agda.Interaction.Highlighting.LaTeX as LaTeX
import Agda.Interaction.Highlighting.HTML

import Agda.TypeChecker
import Agda.TypeChecking.Monad hiding (MetaInfo, Constructor)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors
import qualified Agda.TypeChecking.Serialise
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.SizedTypes

import Agda.Compiler.MAlonzo.Compiler as MAlonzo
import Agda.Compiler.Epic.Compiler as Epic
import Agda.Compiler.JS.Compiler as JS

import Agda.Termination.TermCheck

import Agda.Utils.Monad
import Agda.Utils.FileName
import Agda.Utils.Pretty
import qualified Agda.Utils.IO.UTF8 as UTF8

import Agda.Tests
import Agda.Version

import qualified System.IO as IO

checkFile :: AbsolutePath -> TCM TopLevelModuleName
checkFile file = do resetState
                    (i, mw) <- Imp.typeCheck file
                    case mw of
                        Nothing -> return (toTopLevelModuleName (iModuleName i))
                        Just (Warnings _ unsolved@(_:_) _) ->
                            typeError (UnsolvedMetas unsolved)
                        Just (Warnings _ _ unsolved@(_:_)) ->
                            typeError (UnsolvedConstraints unsolved)
                        Just (Warnings termErrs@(_:_) _ _) ->
                            typeError (TerminationCheckFailed termErrs)
                        _ -> error "The impossible happened"

getModule :: TopLevelModuleName -> TCM (HighlightingInfo, String)
getModule m =
    do Just mi <- getVisitedModule m
       Just f <- Map.lookup m . stModuleToSource <$> get
       s <- liftIO . UTF8.readTextFile . filePath $ f
       return (iHighlighting (miInterface mi), s)

pairPositions :: HighlightingInfo -> String -> [(Integer, String, MetaInfo)]
pairPositions info contents =
    map (\cs@((mi, (pos, _)) : _) -> (pos, map (snd . snd) cs, maybe mempty id mi)) .
    groupBy ((==) `on` fst) .
    map (\(pos, c) -> (Map.lookup pos infoMap, (pos, c))) .
    zip [1..] $
    contents
  where
    infoMap = toMap (decompress info)

-- TODO make these more accurate
beginCode :: String -> MetaInfo -> Bool
beginCode s _ = isInfixOf "\\begin{code}" s

endCode :: String -> MetaInfo -> Bool
endCode s _ = isInfixOf "\\end{code}" s

groupLiterate :: [(Integer, String, MetaInfo)]
              -> [Either String [(Integer, String, MetaInfo)]]
groupLiterate = begin
  where
    -- TODO Make the spacing cleaner
    begin contents =
        let (com, rest) = span (notCode beginCode) contents
        in Left ("\n\n" ++ concat [s | (_, s, _) <- com] ++ "\n\n") : end rest

    end []  = []
    end mis =
        case span (notCode endCode) mis of
            (a, e : b) -> Right (a ++ [e]) : begin b
            _          -> error "malformed file"


    notCode :: (String -> MetaInfo -> Bool) -> (Integer, String, MetaInfo) -> Bool
    notCode f (_, s, mi) = not (f s mi)

annotate :: TopLevelModuleName -> Integer -> MetaInfo -> Html -> Html
annotate m pos mi = anchor ! attributes
  where
    attributes =
        [name (show pos)] ++
        fromMaybe [] (definitionSite mi >>= link) ++
        (case classes of
          [] -> []
          cs -> [theclass $ unwords cs])

    classes =
        maybe [] noteClasses (note mi)
        ++ otherAspectClasses (otherAspects mi)
        ++ maybe [] aspectClasses (aspect mi)

    aspectClasses (Name mKind op) =
        let kindClass = maybe [] ((: []) . showKind) mKind

            showKind (Constructor Inductive)   = "InductiveConstructor"
            showKind (Constructor CoInductive) = "CoinductiveConstructor"
            showKind k                         = show k

            opClass = if op then ["Operator"] else []
        in kindClass ++ opClass
    aspectClasses a = [show a]

    otherAspectClasses = map show

    -- Notes are not included.
    noteClasses _ = []

    link (m', pos') = if m == m' then Just [href $ "#" ++ show pos'] else Nothing

toMarkdown :: TopLevelModuleName -> [Either String [(Integer, String, MetaInfo)]]
          -> String
toMarkdown m contents =
    concat [ case c of
                  Left s   -> s
                  Right cs ->
                      renderHtmlFragment . pre . mconcat $
                      [(annotate m pos mi (stringToHtml s)) | (pos, s, mi) <- cs]
           | c <- contents ]

convert :: TopLevelModuleName -> TCM String
convert m =
    do (info, contents) <- getModule m
       return . toMarkdown m . groupLiterate . pairPositions info $ contents

htmlAgda :: CommandLineOptions -> FilePath -> IO String
htmlAgda opts fp =
    do r <- runTCM $ catchError (setCommandLineOptions opts >>
                                 checkFile (mkAbsolute fp) >>= convert)
                   $ \err -> do s <- prettyError err
                                liftIO (putStrLn s)
                                throwError err
       case r of
           Right s -> return s
           Left _  -> exitFailure
