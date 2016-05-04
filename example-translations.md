

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
fmod DATA-MAYBE{a :: TRIV} is
    sort Maybe{a} .
    op Nothing : -> Maybe{a} .
    op Just_ : a$Elt -> Maybe{a} .
endfm
```

Translating Classes
-------------------

```haskell
class Functor (f :: * -> *) where
    fmap :: (a -> b) -> f a -> f b
```

```maude
fmod CLASS-FUNCTOR{a :: TRIV, b :: TRIV, f :: DATA-CONST} is
    protecting FUNCTIONS{a,b} .
    protecting FUNCTIONS{f{a},f{b}} .
    protecting FUNCTIONS{FUNCTION{a,b},FUNCTION{f{a},f{b}}} .
    op fmap : -> =>{=>{a,b},=>{f{a},f{b}}} .
endfm
```

Translating Instances
---------------------

```haskell
instance Functor Maybe where
    fmap f Nothing = Nothing
    fmap f (Just a) = Just (f a)
```


```maude
fmod INSTANCE-FUNCTOR-MAYBE{a :: TRIV, b :: TRIV} is
    protecting CLASS-FUNCTOR{a,b,DATA-MAYBE} .
    protecting DATA-MAYBE{a} .
    protecting DATA-MAYBE{b} .
    var f : =>{a,b} .
    var a : a$Elt .
    eq fmap f Nothing = Nothing .
    eq fmap f (Just a) = Just (f a) .
endfm


fmod MAYBE{a :: TRIV, b :: TRIV} is
    protecting INSTANCE-FUNCTOR-MAYBE{a, b} .
    protecting INSTANCE-FUNCTOR-MAYBE{b, a} .
    ---protecting INSTANCE-APPLICATIVE-MAYBE{a, b} .
    ---protecting INSTANCE-APPLICATIVE-MAYBE{b, a} .
endfm
```










