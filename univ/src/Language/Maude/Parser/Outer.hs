module Language.Maude.Parser.Outer where

import Debug.Trace
import Control.Compose (OO(OO))
import Data.Char (isSpace)
import Data.List (intercalate, stripPrefix, isPrefixOf)
import qualified Text.Regex.Applicative as RE
import GLL.Combinators.Interface hiding (char, lexer, whitespace)
import Language.Maude.Types

acceptableChars :: String
acceptableChars = [' '..'z'] ++ "\n"

whitespace :: String
whitespace = " \n\t"

ws :: AltExpr Token String
ws = id <$$> multiple (OO . map char $ whitespace)

ws1 :: AltExpr Token String
ws1 = id <$$> multiple1 (OO . map char $ whitespace)

lexer :: String -> [Token]
lexer = map Char

char :: Char -> AltExpr Token Char
char c = c <$$ keychar c

anyChar :: AltExprs Token Char
anyChar = OO . map char $ acceptableChars

word :: String -> AltExpr Token String
word []    = satisfy []
word (c:s) = (:) <$$> char c <**> word s

wsWord :: String -> AltExpr Token String
wsWord s = ws **> word s

ws1Word :: String -> AltExpr Token String
ws1Word s = ws1 **> word s

anyWord :: AltExpr Token String
anyWord = id <$$> some anyChar

wsAnyWord :: AltExpr Token String
wsAnyWord = ws **> anyWord

ws1AnyWord :: AltExpr Token String
ws1AnyWord = ws1 **> anyWord

anyWordWithin :: (String, String) -> AltExpr Token String
anyWordWithin (begin, end) = word begin **> anyWord <** word end

stripChunk :: (String, String) -> AltExpr Token String
stripChunk (begin, end) = (++) <$$> anyWord <** anyWordWithin (begin, end) <**> anyWord

stripChunkWellNested :: (String, String) -> AltExpr Token String
stripChunkWellNested (begin, end) = (++) <$$> anyWord <** word begin **> scwn 1
    where
        scwn 0 = stripChunkWellNested (begin, end)
        scwn n = id <$$> (    word end   **> scwn (n-1)
                         <||> word begin **> scwn (n+1)
                         )

fixParser :: AltExpr Token String -> String -> String
fixParser p input = case parse p . lexer $ input of
                        []         -> input
                        (rest : _) -> fixParser p rest

--- strip non-nesting comments (an alternative implemtation wouldn't even go through the parser)
stripCommentsUsingParser :: (String, String, String) -> String -> String
stripCommentsUsingParser (beginBlock, endBlock, beginLine) = fixParser (stripChunk (beginBlock, endBlock)) . fixParser (stripChunk (beginLine, "\n"))

--- Taken from `GLL.Combinators.Lexer` (takes into account nesting)
stripComments :: (String, String, String) -> String -> String
stripComments (start, end, line) input = stripComments' 0 input
    where
        stripComments' _ []                                    = []
        stripComments' n input      | start `isPrefixOf` input = stripComments' (n+1) (drop (length start) input)
        stripComments' 0 input      | line  `isPrefixOf` input = stripComments' 0     (tail . dropWhile (/= '\n') $ input)
        stripComments' 0 (i : rest)                            = i : stripComments' 0 rest
        stripComments' n input      | end   `isPrefixOf` input = stripComments' (n-1) (drop (length end) input)
        stripCommetns' n (i : rest)                            = stripComments' n rest

data ModSkeleton = FModSkeleton String String
                 | UModSkeleton String String
                 deriving Show

pModSkeleton :: (String -> String -> ModSkeleton) -> (String, String) -> AltExpr Token ModSkeleton
pModSkeleton ctor (begin, end) = wsWord begin **> (ctor <$$> ws1AnyWord <** ws1Word "is" <**> ws1AnyWord) <** ws1Word end

pModuleSkeleton :: BNF Token ModSkeleton
pModuleSkeleton = "Module Skeleton" <::=> pModSkeleton FModSkeleton ("fmod", "endfm")
                                     <||> pModSkeleton UModSkeleton ("umod", "endum")

---maudeLexer :: LexerSettings
---maudeLexer = LexerSettings { keychars          = ""
---                           , keywords          = [ "fmod", "endfm", "umod", "endum", "is"
---                                                 , "is", "protecting", "extending", "including", "using"
---                                                 , "sort", "sorts", "subsort", "subsorts", "<", "$"
---                                                 , "op", "ops", ":", "->", "[", "]", "."
---                                                 , "ctor", "assoc", "comm", "ditto", "id:", "prec", "custom"
---                                                 , "forall", "exists"
---                                                 ]
---                           , whitespace        = isSpace
---                           , lineComment       = "---"
---                           , blockCommentOpen  = "---("
---                           , blockCommentClose = ")---"
---                           , identifiers       = RE.some $ RE.psym (`elem` identChars)
---                           , altIdentifiers    = RE.some $ RE.psym (`elem` identChars)
---                           , tokens            = []
---                           }
---
---keywordAsLit :: (String -> a) -> AltExprs Token a
---keywordAsLit f = OO . map (\kw -> f kw <$$ keyword kw) $ keywords maudeLexer
---
---pSort :: BNF Token Sort
---pSort = "Sort" <::=> keyword "[" **> (K <$$> pSort) <** keyword "]"
---                <||> keyword "$" **> (V <$$> pSort)
---                <||> G   <$$> (id_lit <||> keywordAsLit id)
---                <||> SOp <$$> pSort <** keychar '{' <**> (multipleSepBy pSort $ keychar ',') <** keychar '}'
---
---pSortDecl :: BNF Token Decl
---pSortDecl = "Sort Declaration" <::=> (keyword "sort" <||> keyword "sorts") **> (Sorts <$$> many1 pSort) <** keyword "."
---
---pSubSortDecl :: BNF Token Decl
---pSubSortDecl = "SubSorts Declaration" <::=> (keyword "subsort" <||> keyword "subsorts") **> (SubSorts <$$> manySepBy1 (many1 pSort) (keyword "<")) <** keyword "."
---
---pAttribute :: BNF Token Attribute
---pAttribute = "Attribute" <::=> Ctor  <$$ keyword "ctor"
---                          <||> Assoc <$$ keyword "assoc"
---                          <||> Comm  <$$ keyword "comm"
---                          <||> Ditto <$$ keyword "ditto"
---                          <||> keyword "id:"    **> (Id     <$$> (id_lit <||> (show <$$> int_lit)))
---                          <||> keyword "prec"   **> (Prec   <$$> int_lit)
---                          <||> keyword "custom" **> (Custom <$$> (id_lit <||> keywordAsLit id))
---
---pProductionItem :: BNF Token ProductionItem
---pProductionItem = "Production Item" <::=> Hole       <$$  keyword "_"
---                                     <||> Lit        <$$> id_lit
---                                     <||> keywordAsLit Lit
---
---pOpDecl :: BNF Token Decl
---pOpDecl = let production = many1 pProductionItem
---              arity      = (,) <$$> many pSort <** keyword "->" <**> pSort
---              attributes = optionalWithDef (keyword "[" **> many pAttribute <** keyword "]") []
---          in  "Operator Declaration" <::=> keyword "op" **> (Op <$$> production <** keyword ":" <**> arity <**> attributes) <** keyword "."
---
---pSigDecl :: BNF Token Decl
---pSigDecl = "Signature Declaration" <::=> pOpDecl <||> pSortDecl <||> pSubSortDecl
---
---pImport :: BNF Token Import
---pImport = "Import Statement" <::=> keyword "protecting" **> (Protecting <$$> id_lit) <** keyword "."
---                              <||> keyword "extending"  **> (Extending  <$$> id_lit) <** keyword "."
---                              <||> keyword "including"  **> (Including  <$$> id_lit) <** keyword "."
---                              <||> keyword "using"      **> (Using      <$$> id_lit) <** keyword "."
---
---pUniv :: BNF Token ([Decl], [Decl])
---pUniv = "Universal Construction" <::=> keyword "forall" **> ((,) <$$> many pSigDecl <** keyword "exists" <**> many pSigDecl)
---
---pModule :: BNF Token Module
---pModule = "Module" <::=> keyword "fmod" **> (FMod <$$> id_lit <** keyword "is" <**> many pImport <**> many pSigDecl) <** keyword "endfm"
---                    <||> keyword "umod" **> (UMod <$$> id_lit <** keyword "is" <**> many pImport <**> many pUniv)    <** keyword "endum"
---
