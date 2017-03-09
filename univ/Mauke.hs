{-# LANGUAGE TemplateHaskell #-}


module Mauke where

import Data.List (intersperse)
import Data.Char (isDigit, isSpace, isAlpha, isUpper, isLower)
import Control.Monad (replicateM)
import Language.Haskell.TH
import GLL.Combinators.Interface

data OpToken = Lit String
             | Space
             | Hole
             --- | TT Token
             deriving Show

--- instance SubsumesToken OpToken where
---     upcast = TT
---     downcast (Lit str) = Just $ StringLit (Just str)
---     downcast Space     = Just $ Keyword " "
---     downcast Hole      = Just $ Keyword "hole"

specialChar :: Char -> Bool
specialChar '_'  = True
specialChar '\\' = True
specialChar c    = isSpace c

lexOpStr :: String -> [OpToken]
lexOpStr ""           = []
lexOpStr ('_' : rest) = Hole : lexOpStr rest
lexOpStr (c : rest)
    | isSpace c       = Space : lexOpStr (dropWhile isSpace rest)
lexOpStr ('\\' : c : rest)
    | specialChar c   = case lexOpStr rest of
                            (Lit l : rest') -> Lit (c : l) : rest'
                            rest'           -> Lit [c] : rest'
lexOpStr opStr        = let lit  = takeWhile (not . specialChar) opStr
                            rest = dropWhile (not . specialChar) opStr
                        in  case lexOpStr rest of
                                (Lit l : rest') -> Lit (lit ++ l) : rest'
                                rest'           -> Lit lit : rest'

mkParserKeyword :: [Char] -> Q Exp
mkParserKeyword []     = error "Cannot parse empty keywords."
mkParserKeyword (c:cs) = let kwParser = foldl (\e c -> [e| $e **> keychar c |]) [e| keychar c |] cs
                         in  [e| (c:cs) <$$ $kwParser |]

mkParserAnyOf :: [Char] -> Q Exp
mkParserAnyOf []     = error "Must supply at least one alternative to 'mkParserAnyOf'."
mkParserAnyOf (c:cs) = foldl (\e c -> [e| $e <||> keychar c |]) [e| keychar c |] cs

mkParserOpToken :: OpToken -> Q Exp
mkParserOpToken (Lit str) = mkParserKeyword str
mkParserOpToken Space     = [e| many $(mkParserAnyOf " \n\t") |]
mkParserOpToken Hole      = let --- chars = mkParserAnyOf $ ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ "+-*/"
                                chars = mkParserAnyOf $ ['0'..'9'] ++ "+-*/ "
                            in  [e| many $chars |]

mkParserOp :: [OpToken] -> Q Exp
mkParserOp [] = error "Empty productions not allowed."
mkParserOp ps = let lastP  = [e| (:[]) <$$> $(mkParserOpToken $ last ps) |]
                    initPs = map (\o -> [e| (:) <$$> $(mkParserOpToken o) |]) $ init ps
                in  foldr (\p1 p2 -> [e| $p1 <**> $p2 |]) lastP initPs
