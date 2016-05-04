

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
```

```maude
fmod MAYBE{a :: TRIV} is
    sort Maybe{a} .
    op Nothing : -> Maybe{a} .
    op Just_ : a$Elt -> Maybe{a} .
endfm
```

Translating Classes
-------------------

```haskell
class Functor f where
    fmap :: (a -> b) -> f a -> f b
```

```maude
fmod FUNCTOR{a :: TRIV, b :: TRIV} is
    protecting FUNCTION{a,b} .
    sorts Functor{a} Functor{b} .
    op fmap__ : =>{a,b} Functor{a} -> Functor{b} .
    op fmap_  : =>{a,b} -> =>{Functor{a},Functor{b}} .
endfm
```

Translating Instances
---------------------
