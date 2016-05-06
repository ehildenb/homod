

Implicitely Exists
------------------

```maude
fmod SET-FUNCTION{X :: TRIV, Y :: TRIV} is
    sorts =>{X,Y} .
    op __ : =>{X,Y} X$Elt -> Y$Elt .
endfm

fmod SET-FUNCTION-ID{X :: TRIV} is
    protecting SET-FUNCTION{X,X} .
    op id : -> =>{X,X} .
    var x : X$Elt .
    eq id x = x .
endfm

fmod FUNCTIONS{X :: TRIV, Y :: TRIV} is
    protecting SET-FUNCTION{X,Y} .
    protecting SET-FUNCTION{Y,X} .
    protecting SET-FUNCTION-ID{X} .
    protecting SET-FUNCTION-ID{Y} .
endfm
```

Translating Data-types
----------------------

```haskell
data Maybe a = Just a
             | Nothing

data Cons a = []
            | a : Cons a
```

Translating Classes and Instances
-------------------

```haskell
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
```










