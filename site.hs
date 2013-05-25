{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
import           Control.Monad (filterM)
import           Data.Monoid ((<>))

import           Agda.Interaction.Options (CommandLineOptions(..), defaultOptions)
import           Hakyll
import           Hakyll.Web.Agda

main :: IO ()
main =
    hakyll $
    do -- Assets
       match ("images/*" .||. "css/*" .||. "js/*" .||. "fonts/*") $
           do route idRoute; compile copyFileCompiler

       -- Templates
       match "templates/*" $ compile templateCompiler

       -- Posts
       let agdaComp = pandocAgdaCompilerWith defaultHakyllReaderOptions
                                             defaultHakyllWriterOptions
                                             agdaOpts
       match ("posts/*.md" .||. "posts/*.lagda" .||. "posts/*.lhs") $
           do route $ setExtension "html"
              compile $ agdaComp                                              >>=
                        loadAndApplyTemplate "templates/post.html"    postCtx >>=
                        saveSnapshot "content"                                >>=
                        loadAndApplyTemplate "templates/default.html" postCtx >>=
                        relativizeUrls

       -- Archive
       create ["archive.html"] $
           do route idRoute
              compile $
                  let archiveCtx = field "posts" (\_ -> postList recentFirst) <>
                                   constField "title" "index"                 <>
                                   defaultContext
                  in  makeItem ""                                              >>=
                      loadAndApplyTemplate "templates/archive.html" archiveCtx >>=
                      loadAndApplyTemplate "templates/default.html" archiveCtx >>=
                      relativizeUrls

       -- Splash page
       match "index.html" $
           do route idRoute; compile $ getResourceBody >>= relativizeUrls

       -- RSS and Atom
       create ["atom.xml"] $ renderFeed renderAtom
       create ["rss.xml"]  $ renderFeed renderRss

       -- CV
       match "cv/*" $ do route idRoute; compile copyFileCompiler

postCtx :: Context String
postCtx = dateField "date" "%Y-%m-%d" <> defaultContext

postList :: ([Item String] -> Compiler [Item String]) -> Compiler String
postList sortFilter =
    do posts   <- filterM isPublished =<< sortFilter =<< loadAll "posts/*"
       itemTpl <- loadBody "templates/post-item.html"
       list    <- applyTemplateList itemTpl postCtx posts
       return list

isPublished :: MonadMetadata m => Item a -> m Bool
isPublished (itemIdentifier -> ident) =
    do publishedM <- getMetadataField ident "published"
       case publishedM of
           Nothing      -> return True
           Just "false" -> return False
           Just s       -> fail ("invalid `published' metadata value: " ++ s)

renderFeed
    :: (FeedConfiguration -> Context String -> [Item String] -> Compiler (Item String))
    -> Rules ()
renderFeed f =
    do route idRoute
       compile $ do let feedCtx = postCtx <> bodyField "description"
                    posts <- fmap (take 10) . recentFirst =<< filterM isPublished =<<
                             loadAllSnapshots "posts/*" "content"
                    f feedConf feedCtx posts

feedConf :: FeedConfiguration
feedConf = FeedConfiguration
    { feedTitle       = "bitonic's blog."
    , feedDescription = "Computers, with a PL theory slant."
    , feedAuthorName  = "Francesco Mazzoli"
    , feedAuthorEmail = "f@mazzo.li"
    , feedRoot        = "http://mazzo.li"
    }

agdaOpts :: CommandLineOptions
agdaOpts = defaultOptions {optIncludeDirs = Left [".", "/home/bitonic/src/agda-lib/src"]}