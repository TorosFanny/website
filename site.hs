{-# LANGUAGE OverloadedStrings #-}
import           Data.Monoid ((<>))
import           Hakyll

main :: IO ()
main =
    hakyll $
    do match "images/*" $ do route idRoute; compile copyFileCompiler
       match "css/*"    $ do route idRoute; compile copyFileCompiler
       match "js/*"     $ do route idRoute; compile copyFileCompiler
       match "fonts/*"  $ do route idRoute; compile copyFileCompiler

       match "posts/*" $
           do route $ setExtension "html"
              compile $ pandocCompiler                                        >>=
                        loadAndApplyTemplate "templates/post.html"    postCtx >>=
                        loadAndApplyTemplate "templates/default.html" postCtx >>=
                        relativizeUrls

       create ["archive.html"] $
           do route idRoute
              compile $
                  let archiveCtx = field "posts" (\_ -> postList recentFirst) <>
                                   constField "title" "index"                 <>
                                   defaultContext
                  in makeItem ""                                              >>=
                     loadAndApplyTemplate "templates/archive.html" archiveCtx >>=
                     loadAndApplyTemplate "templates/default.html" archiveCtx >>=
                     relativizeUrls

       match "templates/*" $ compile templateCompiler

       match "index.html" $
           do route idRoute
              compile $ getResourceBody >>= relativizeUrls

postCtx :: Context String
postCtx = dateField "date" "%B %e, %Y" <> defaultContext

postList :: ([Item String] -> Compiler [Item String]) -> Compiler String
postList sortFilter =
    do posts   <- sortFilter =<< loadAll "posts/*"
       itemTpl <- loadBody "templates/post-item.html"
       list    <- applyTemplateList itemTpl postCtx posts
       return list
