import Text.Pandoc

autoLink :: Inline -> Inline
autoLink (Link ils tg) = Link [Code nullAttr (concat [s | Str s <- ils])] tg
autoLink il            = il

strongToEmph :: Inline -> Inline
strongToEmph (Strong ils) = Emph ils
strongToEmph il           = il

stripImages :: Inline -> [Inline]
stripImages (Image ils _) = ils
stripImages il            = [il]

transformDoc :: Pandoc -> Pandoc
transformDoc = bottomUp (concatMap stripImages) . bottomUp (strongToEmph . autoLink)

readDoc :: String -> Pandoc
readDoc = readHtml def

writeDoc :: Pandoc -> String
writeDoc = writeMarkdown def

main :: IO ()
main = interact (writeDoc . transformDoc . readDoc)
