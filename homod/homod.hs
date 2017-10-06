--- Original Haskell
--- ================


module HaskTest where

import Prelude hiding (Foldable, Maybe, map, Just, Nothing, foldl)

data Maybe a = Just a
             | Nothing
             deriving Show

infixr 5 :|
data Cons a = Nil
            | a :| Cons a
            deriving Show

class Mappable f where
    map :: (a -> b) -> f a -> f b

instance Mappable Maybe where
    map f Nothing = Nothing
    map f (Just a) = Just (f a)

instance Mappable Cons where
    map f Nil = Nil
    map f (a :| as) = f a :| map f as

class Foldable f where
    foldl :: (b -> a -> b) -> b -> f a -> b

instance Foldable Cons where
    foldl f b Nil = b
    foldl f b (a :| as) = foldl f (f b a) as


--- Above is an example of two common Haskell algebraic datatypes; the `Maybe`
--- datatype specifies the possible absence of data/result and the `Cons` datatype
--- represents a singly-linked list. In addition, the typeclasses `Mappable` and
--- `Foldable` are defined. We've provided `Mappable` instances for both `Maybe` and
--- `Cons`, which amounts to defining the function `map` for each of them. We've
--- also provided a `Foldable` instance for `Cons`. Note that both `map` and `foldl`
--- above are higher order functions, and that when using `map`, you must infer
--- whether you are mapping over a `Cons` or a `Maybe`.

--- We would like to be able to use Haskell-like higher order code within Maude, or
--- even be able to use the above code directly in Maude. The following sections
--- discuss how this and similar higher order Haskell modules can be converted into
--- equivalent Maude modules.
