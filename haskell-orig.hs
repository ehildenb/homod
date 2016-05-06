module HaskTest where

data Maybe a = Just a
             | Nothing

data Cons a = []
            | a : Cons a
class Mapable (f :: * -> *) where
    map :: (a -> b) -> f a -> f b

instance Mappable Maybe where
    map f Nothing = Nothing
    map f (Just a) = Just (f a)

instance Mappable Cons where
    map f [] = []
    map f (a : as) = f a : fmap f as

class Foldable (f :: * -> *) where
    foldl :: (b -> a -> b) -> b -> f a -> b

instance Foldable Cons where
    foldl f b [] = b
    foldl f b (a : as) = foldl f (f b a) as
