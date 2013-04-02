{-# LANGUAGE OverloadedStrings #-}
import           Data.Monoid ((<>))
import           Hakyll
import           LiterateAgda

main :: IO ()
main =
    hakyll $
    do -- Assets
       match "images/*" $ do route idRoute; compile copyFileCompiler
       match "css/*"    $ do route idRoute; compile copyFileCompiler
       match "js/*"     $ do route idRoute; compile copyFileCompiler
       match "fonts/*"  $ do route idRoute; compile copyFileCompiler

       -- Templates
       match "templates/*" $ compile templateCompiler

       -- Posts
       match ("posts/*.md" .||. "posts/*.lagda" .||. "posts/*.lhs") $
           do route $ setExtension "html"
              compile $ pandocAgdaCompiler                                    >>=
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
postCtx = dateField "date" "%B %e, %Y" <> defaultContext

postList :: ([Item String] -> Compiler [Item String]) -> Compiler String
postList sortFilter =
    do posts   <- sortFilter =<< loadAll "posts/*"
       itemTpl <- loadBody "templates/post-item.html"
       list    <- applyTemplateList itemTpl postCtx posts
       return list

renderFeed
    :: (FeedConfiguration -> Context String -> [Item String] -> Compiler (Item String))
    -> Rules ()
renderFeed f =
    do route idRoute
       compile $ do let feedCtx = postCtx <> bodyField "description"
                    posts <- fmap (take 10) . recentFirst =<<
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
