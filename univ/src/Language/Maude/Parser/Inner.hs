module Language.Maude.Parser.Inner where

import Data.Char (isSpace)
import Data.List (intercalate)
import qualified Text.Regex.Applicative as RE
import GLL.Combinators.Interface
import Language.Maude.Types

identChars :: String
identChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789*/-+|<>={}[]$.,:- \t\n"

charLexer :: LexerSettings
charLexer = LexerSettings { keychars          = ""
                          , keywords          = []
                          , whitespace        = \_ -> False
                          , lineComment       = "---"
                          , blockCommentOpen  = "---("
                          , blockCommentClose = ")---"
                          , identifiers       = fmap (: []) $ RE.psym (`elem` identChars)
                          , altIdentifiers    = fmap (: []) $ RE.psym (\_ -> False)
                          , tokens            = []
                          }

--- pBubble :: BNF Token [Token]
--- pBubble = many id_lit
