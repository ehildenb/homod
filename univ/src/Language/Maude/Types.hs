module Language.Maude.Types where

import Data.List (intercalate)
        
data ProductionItem = Lit String
                    | Space
                    | Hole
                    deriving Eq

instance Show ProductionItem where
    show (Lit s) = s
    show Space   = " "
    show Hole    = "_"

data Sort = V Sort
          | K Sort
          | G String
          | SOp Sort [Sort]
          deriving Eq

instance Show Sort where
    show (V s)      = "$" ++ show s
    show (K s)      = "[" ++ show s ++ "]"
    show (G s)      = s
    show (SOp s ss) = show s ++ "{" ++ (intercalate "," . map show $ ss) ++ "}"

--- data SortDecl = Sorts [Sort]
---               deriving (Eq, Show)

--- data SubSortDecl = SubSorts [[Sort]]
---                  deriving (Eq, Show)

data Attribute = Ctor | Assoc | Comm | Ditto
               | Id String | Prec Int | Custom String
               deriving Eq

instance Show Attribute where
    show Ctor       = "ctor"
    show Assoc      = "assoc"
    show Comm       = "comm"
    show Ditto      = "ditto"
    show (Id s)     = "id: " ++ s
    show (Prec i)   = "prec " ++ show i
    show (Custom s) = s

--- data OpDecl = Op Production [Sort] Sort Attributes
---             deriving (Eq, Show)

data Decl = Sorts    [Sort]                           
          | SubSorts [[Sort]]                         
          | Op       [ProductionItem] ([Sort], Sort) [Attribute]
          deriving Eq

showListSepBy :: Show a => String -> [a] -> String
showListSepBy s = intercalate s . map show

instance Show Decl where
    show (Sorts ss)            = "sorts " ++ showListSepBy " " ss ++ " ."
    show (SubSorts ss)         = "subsorts " ++ (intercalate " < " . map (showListSepBy " ") $ ss) ++ " ."
    show (Op pis (ss, s) [])   = "op " ++ concatMap show pis ++ " : " ++ showListSepBy " " ss ++ " -> " ++ show s ++ " ."
    show (Op pis (ss, s) atts) = "op " ++ concatMap show pis ++ " : " ++ showListSepBy " " ss ++ " -> " ++ show s ++ " [" ++ showListSepBy " " atts ++ "] ."

showIndentList :: Show a => Int -> [a] -> String
showIndentList n = concatMap (\d -> replicate n ' ' ++ show d ++ "\n")

data Import = Protecting String
            | Extending  String
            | Including  String
            | Using      String
            deriving Eq

instance Show Import where
    show (Protecting s) = "protecting " ++ s ++ " ."
    show (Extending s)  = "extending "  ++ s ++ " ."
    show (Including s)  = "including "  ++ s ++ " ."
    show (Using s)      = "using "      ++ s ++ " ."

data Module = FMod String [Import] [Decl]
            | UMod String [Import] [([Decl], [Decl])]
            deriving Eq

instance Show Module where
    show (FMod name imports ds) = "fmod " ++ name ++ " is\n" ++ showIndentList 2 imports ++ "\n" ++ showIndentList 2 ds ++ "endfm"
    show (UMod name imports ds) = let showUnivList (forall, exists) = "  forall\n" ++ showIndentList 4 forall ++ "  exists\n" ++ showIndentList 4 exists
                                  in  "umod " ++ name ++ " is\n" ++ showIndentList 2 imports ++ "\n" ++ concatMap showUnivList ds ++ "endum"

--- data Decl = Sorts [Sort]
---           | SubSort [Sort] Sort
---           |
---           deriving (Eq, Show)
---
--- data Module = Module Sorts SubSorts Opeartors Equations
---             | Univ Module Module
---             | Sequence [Module]
---             deriving (Eq, Show)
