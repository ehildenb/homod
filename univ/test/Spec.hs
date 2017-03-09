module Main where

import System.Exit (exitFailure, exitSuccess)
import Data.List (intercalate)
import Language.Maude.Types
import Language.Maude.Parser.Outer
import GLL.Combinators.Interface (parse, many, Token)

main :: IO ()
main = let t1 = runTest testStripComments
       in  if t1 then exitSuccess else exitFailure

runTest :: Eq a => (String -> a, [(String, a)]) -> Bool
runTest (f, tests) = and . map (\(input, output) -> output == f input) $ tests

testStripComments :: (String -> String, [(String, String)])
testStripComments = ( stripComments ("---(", ")---", "---")
                    , [ ("Outside comment ---( Inside comment )---"                          , "Outside comment ")
                      , ("Outside comment --- Inside comment \n"                             , "Outside comment ")
                      , ("Outside comment ---( Inside comment --- still inside comment )---" , "Outside comment ")
                      , ("Outside comment --- Inside comment --- still inside commment \n"   , "Outside comment ")
                      ]
                    )

--- main :: IO ()
--- main = let t1 = runTest testParseSort
---            t2 = runTest testParseAttribute
---            t3 = runTest testParseProduction
---            t4 = runTest testParseSigDecl
---        in  if and [t1] then exitSuccess else exitFailure
--- 
--- testParseSort :: (String -> Sort, [(String, Sort)])
--- testParseSort = ( head . parse pSort . lexer
---                 , [ ("Nat"                      , G "Nat")
---                   , ("[Nat]"                    , K (G "Nat"))
---                   ---, ("$A"                       , V (G "A"))
---                   ---, ("[$A]"                     , K (V (G "A")))
---                   ---, ("Set{Nat}"                 , SOp (G "Set") [G "Nat"])
---                   ---, ("Set{$A}"                  , SOp (G "Set") [V (G "A")])
---                   ---, ("Set{[$A]}"                , SOp (G "Set") [K (V (G "A"))])
---                   ---, ("Set{$B, [$A], NeSet{$C}}" , SOp (G "Set") [V (G "B"), K (V (G "A")), SOp (G "NeSet") [V (G "C")]])
---                   ---, ("=>{$A,$B}"                , SOp (G "=>")  [V "A", V "B"])
---                   ---, ("$A=>$B"                   , SOp (G "=>")  [V "A", V "B"])
---                   ]
---                 )
--- 
--- testParseAttribute :: (String -> Attribute, [(String, Attribute)])
--- testParseAttribute = ( head . parse pAttribute . lexer maudeLexer
---                      , [ ("ctor"         , Ctor)
---                        , ("assoc"        , Assoc)
---                        , ("comm"         , Comm)
---                        , ("ditto"        , Ditto)
---                        , ("id: mt"       , Id "mt")
---                        ---, ("id: 0"        , Id "0")
---                        , ("prec 98"      , Prec 98)
---                        , ("custom onuth" , Custom "onuth")
---                        ]
---                      )
--- 
--- testParseProduction :: (String -> [ProductionItem], [(String, [ProductionItem])])
--- testParseProduction = ( head . parse (many pProductionItem) . lexer maudeLexer
---                       , [ ("mt"              , [Lit "mt"])
---                         , ("_+_"             , [Hole, Lit "+", Hole])
---                         , ("if_then_else_fi" , [Lit "if", Hole, Lit "then", Hole, Lit "else", Hole, Lit "fi"])
---                         , ("_|->__"          , [Hole, Lit "|->", Hole, Hole])
---                         ---, ("_[_]"            , [Hole, Lit "[", Hole, Lit "]"])
---                         ]
---                       )
--- 
--- testParseSigDecl :: (String -> Decl, [(String, Decl)])
--- testParseSigDecl = ( head . parse pSigDecl . lexer maudeLexer
---                    , [ ("op _+_ : Nat Nat -> Nat [assoc comm id: mt prec 70] ."                  , Op [Hole, Lit "+", Hole] ([G "Nat", G "Nat"], G "Nat") [Assoc, Comm, Id "mt", Prec 70])
---                      , ("op _+_ : Nat Nat -> Nat ."                                              , Op [Hole, Lit "+", Hole] ([G "Nat", G "Nat"], G "Nat") [])
---                      ---, ("op _+_ : Nat Nat -> Nat [assoc comm id: 0 prec 70] ."                   , Op [Hole, Lit "+", Hole] ([G "Nat", G "Nat"], G "Nat") [Assoc, Comm, Id "0", Prec 70])
---                      , ("op if_then_else_fi : Bool Set{Nat} Set{Nat} -> Set{Nat} [assoc comm] ." , Op [Lit "if", Hole, Lit "then", Hole, Lit "else", Hole, Lit "fi"] ([G "Bool", SOp (G "Set") [G "Nat"], SOp (G "Set") [G "Nat"]], SOp (G "Set") [G "Nat"]) [Assoc, Comm])
---                      , ("op if_then_else_fi : Bool Set{Nat} Set{Nat} -> Set{Nat} ."              , Op [Lit "if", Hole, Lit "then", Hole, Lit "else", Hole, Lit "fi"] ([G "Bool", SOp (G "Set") [G "Nat"], SOp (G "Set") [G "Nat"]], SOp (G "Set") [G "Nat"]) [])
---                      ]
---                    )
---  
--- testModule :: String
--- testModule
---     = intercalate "\n" [ "fmod MYMODULE is"
---                        , "  sorts Int Nat ."
---                        , "  subsorts Nat < Int ."
---                        , ""
---                        , "  op 0 : -> Nat [] ."
---                        , "  op s_ : Int -> Int [] ."
---                        , "  op p_ : Int -> Int [] ."
---                        , "endfm"
---                        ]
--- 
--- testUniv :: String
--- testUniv
---     = intercalate "\n" [ "umod SET is"
---                        , ""
---                        , "  forall"
---                        , "    sort $A ."
---                        , "  exists"
---                        , "    sorts NeSet{$A} Set{$A} ."
---                        , "    subsort NeSet{$A} < Set{$A} ."
---                        , "    op mt : -> Set{$A} [] ."
---                        , "    op __ : Set{$A}   Set{$A} -> Set{$A}   [ctor assoc comm id: mt prec 70] ."
---                        , "    op __ : NeSet{$A} Set{$A} -> NeSet{$A} [ctor ditto] ."
---                        , ""
---                        , "  forall"
---                        , "    sorts $A $B NeSet{$A} NeSet{$B} Set{$A} Set{$B} ."
---                        , "    subsort $A < $B ."
---                        , "  exists"
---                        , "    subsort Set{$A} < Set{$B} ."
---                        , "    subsort NeSet{$A} < NeSet{$B} ."
---                        , ""
---                        , "endum"
---                        ]
