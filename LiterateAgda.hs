module LiterateAgda
    ( markdownAgda
    , pandocAgdaCompilerWith
    , pandocAgdaCompiler
    ) where

import           Control.Applicative
import           Data.Char
import           Data.Function
import           Data.List
import           Data.Maybe
import           Data.Monoid

import           Control.Monad.Error
import           Control.Monad.State
import qualified Data.Map as Map
import           System.Directory
import           System.Exit
import           System.FilePath
import           Text.XHtml.Strict

import           Agda.Interaction.Highlighting.Precise
import qualified Agda.Interaction.Imports as Imp
import           Agda.Interaction.Options
import           Agda.Syntax.Abstract.Name (toTopLevelModuleName)
import           Agda.Syntax.Common
import           Agda.Syntax.Concrete.Name (TopLevelModuleName)
import           Agda.TypeChecking.Errors
import           Agda.TypeChecking.Monad hiding (MetaInfo, Constructor)
import           Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import           Hakyll.Core.Compiler
import           Hakyll.Core.Identifier
import           Hakyll.Core.Item
import           Hakyll.Web.Pandoc
import           Text.Pandoc

checkFile :: AbsolutePath -> TCM TopLevelModuleName
checkFile file = do resetState
                    (i, _) <- Imp.typeCheck file
                    return (toTopLevelModuleName (iModuleName i))

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
    -- TODO Make the spacing cleaner, and trim \begin{code} and end
    begin contents =
        let (com, rest) = span (notCode beginCode) contents
        in Left ("\n\n" ++ concat [s | (_, s, _) <- com] ++ "\n\n") :
           trimTop (end rest)

    end []  = []
    end mis =
        case span (notCode endCode) mis of
            (a, e : b) -> Right (a ++ [trimEnd e]) : begin b
            _          -> error "malformed file"

    notCode :: (String -> MetaInfo -> Bool) -> (Integer, String, MetaInfo) -> Bool
    notCode f (_, s, mi) = not (f s mi)

    trimTop (Right ((pos, s, mi) : rs) : rest) =
        Right ((pos, dropWhile isSpace s, mi) : rs) : rest
    trimTop x = x

    trimEnd (pos, s, mi) = (pos, reverse (dropWhile isSpace (reverse s)), mi)

-- Ripped off Agda.Interaction.Highlighting.HTML
annotate :: TopLevelModuleName -> Integer -> MetaInfo -> Html -> Html
annotate m pos mi = anchor ! attributes
  where
    attributes = [name (show pos)] ++
                 fromMaybe [] (definitionSite mi >>= link) ++
                 (case classes of [] -> []; cs -> [theclass (unwords cs)])

    classes = maybe [] noteClasses (note mi) ++
              otherAspectClasses (otherAspects mi) ++
              maybe [] aspectClasses (aspect mi)

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

    link (m', pos') = if m == m'
                      then Just [href ("#" ++ show pos')]
                      else Nothing

toMarkdown :: String
           -> TopLevelModuleName -> [Either String [(Integer, String, MetaInfo)]]
           -> String
toMarkdown classpr m contents =
    concat [ case c of
                  Left s   -> s
                  Right cs ->
                      let h = pre . mconcat $ [ (annotate m pos mi (stringToHtml s))
                                              | (pos, s, mi) <- cs ]
                      in  renderHtmlFragment (h ! [theclass classpr])
           | c <- contents ]

convert :: String -> TopLevelModuleName -> TCM String
convert classpr m =
    do (info, contents) <- getModule m
       return . toMarkdown classpr m . groupLiterate . pairPositions info $ contents

markdownAgda :: CommandLineOptions -> String -> FilePath -> IO String
markdownAgda opts classpr fp =
    do -- We set to the directory of the file, we assume that the agda files are
       -- in one flat directory which is not the one where Hakyll is ran in.
       origDir <- getCurrentDirectory
       setCurrentDirectory (dropFileName fp)
       r <- runTCM $ catchError (setCommandLineOptions opts >>
                                 checkFile (mkAbsolute fp) >>= convert classpr)
                   $ \err -> do s <- prettyError err
                                liftIO (putStrLn s)
                                throwError err
       setCurrentDirectory origDir
       -- TODO try to skip the interface instead of just deleting it
       removeFile (replaceExtension fp "agdai")
       case r of
           Right s -> return (dropWhile isSpace s)
           Left _  -> exitFailure

isAgda :: Item a -> Bool
isAgda i = ex == ".lagda"
  where ex = snd . splitExtension . toFilePath . itemIdentifier $ i

pandocAgdaCompilerWith :: ReaderOptions -> WriterOptions
                       -> Compiler (Item String)
pandocAgdaCompilerWith ropt wopt =
    do i <- getResourceBody
       if isAgda i
          then cached cacheName $
               -- TODO get rid of the unsafePerformIO, and have a more solid way
               -- to get the absolute path
               do it <- getUnderlying; unsafeCompiler $
                      do fp <- (</> toFilePath it) <$> getCurrentDirectory
                         s <- markdownAgda defaultOptions "Agda" fp
                         let i' = i {itemBody = s}
                         return (writePandocWith wopt (readMarkdown ropt <$> i'))
          else pandocCompilerWith ropt wopt
  where cacheName = "LiterateAgda.pandocAgdaCompilerWith"

pandocAgdaCompiler :: Compiler (Item String)
pandocAgdaCompiler =
    pandocAgdaCompilerWith defaultHakyllReaderOptions defaultHakyllWriterOptions
