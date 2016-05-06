---
author: Everett Hildenbrandt, Lucas Pena
title: Generating Higher-order Maude from Haskell
format: latex
geometry: margin=2.0cm
execute: maude-gen.maude haskell-orig.hs
...


Original Haskell
================

These are data-declarations we would like to make:

```haskell{exec:haskell-orig.hs}
module HaskTest where

data Maybe a = Just a
             | Nothing

data Cons a = []
            | a : Cons a
```

And some type-class instances for them:

```haskell{exec:haskell-orig.hs}
class Mappable (f :: * -> *) where
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

\newpage

Maude Code
==========

Pre-Exists
----------

```maude{exec:maude-gen.maude}
fmod FUNCTION{X :: TRIV, Y :: TRIV} is
    sorts =>{X,Y} .
    op __ : =>{X,Y} X$Elt -> Y$Elt .
endfm

fmod FUNCTION-ID{X :: TRIV} is
    protecting FUNCTION{X,X} .
    op id : -> =>{X,X} .
    var x : X$Elt .
    eq id x = x .
endfm

fmod FUNCTION-COMP{X :: TRIV, Y :: TRIV, Z :: TRIV} is
    protecting FUNCTION{X,Y} .
    protecting FUNCTION{Y,Z} .
    protecting FUNCTION{X,Z} .

    op _._ : =>{Y,Z} =>{X,Y} -> =>{X,Z} [gather (E e)].

    var f : =>{X,Y} .
    var g : =>{Y,Z} .
    var x : X$Elt .
    eq (g . f) x = g (f x) .
endfm
```

Generated
---------

Note that we can't actually generate this code yet - this is what we would like
to generate given the specification above.

### Core Maude

```maude{exec:maude-gen.maude}
fmod DATA-MAYBE{a :: TRIV} is
    sort Maybe{a} .
    op Nothing : -> Maybe{a} .
    op Just_ : a$Elt -> Maybe{a} .
endfm

fmod DATA-CONS{a :: TRIV} is
    sort Cons{a} .
    op [] : -> Cons{a} .
    op _:_ : a$Elt Cons{a} -> Cons{a} .
endfm
```

\newpage

### Full Maude

```maude{exec:maude-gen.maude}
load fm27.maude .

(
view Maybe{a :: TRIV} from TRIV to DATA-MAYBE{a} is
    sort Elt to Maybe{a} .
endv
)

(
view Cons{a :: TRIV} from TRIV to DATA-CONS{a} is
    sort Elt to Cons{a} .
endv
)

(
view =>{X :: TRIV, Y :: TRIV} from TRIV to FUNCTION{X,Y} is
    sort Elt to =>{X,Y} .
endv
)

(
fmod INSTANCE-MAPPABLE-MAYBE{a :: TRIV, b :: TRIV} is
    protecting FUNCTION{a, b} .
    protecting FUNCTION{Maybe{a}, Maybe{b}} .
    extending FUNCTION{=>{a,b}, =>{Maybe{a},Maybe{b}}} .

    op map : -> =>{=>{a,b}, =>{Maybe{a},Maybe{b}}} .

    var f : =>{a,b} .
    var a : a$Elt .
    eq map f Nothing = Nothing .
    eq map f (Just a) = Just (f a) .
endfm
)

(
fmod INSTANCE-MAPPABLE-CONS{a :: TRIV, b :: TRIV} is
    protecting FUNCTION{a, b} .
    protecting FUNCTION{Cons{a}, Cons{b}} .
    extending FUNCTION{=>{a,b}, =>{Cons{a},Cons{b}}} .

    op map : -> =>{=>{a,b}, =>{Cons{a},Cons{b}}} .

    var f   : =>{a,b} .
    var a   : a$Elt .
    var as  : Cons{a} .
    eq map f [] = [] .
    eq map f (a : as) = f a : map f as .
endfm
)

(
fmod INSTANCE-FOLDABLE-CONS{a :: TRIV, b :: TRIV} is
    protecting FUNCTION{a, b} .
    protecting FUNCTION{b, =>{a,b}} .
    protecting FUNCTION{Cons{a}, b} .
    protecting FUNCTION{b, =>{Cons{a}, b}} .
    extending FUNCTION{=>{b, =>{a,b}}, =>{b, =>{Cons{a}, b}}} .

    op foldl : -> =>{=>{b,=>{a,b}}, =>{b, =>{Cons{a}, b}}} .

    var f   : =>{b, =>{a,b}} .
    var b   : b$Elt .
    var a   : a$Elt .
    var as  : Cons{a} .

    eq foldl f b [] = b .
    eq foldl f b (a : as) = foldl f (f b a) as .
endfm
)
```
\newpage

Testing
-------

```maude{exec:maude-gen.maude}
(
fmod TESTING is
    extending INSTANCE-MAPPABLE-MAYBE{Nat, Bool} .
    extending INSTANCE-MAPPABLE-CONS{Nat, Nat} .
    extending INSTANCE-MAPPABLE-CONS{Nat, Bool} .
    extending INSTANCE-FOLDABLE-CONS{Bool, Bool} .
    extending INSTANCE-FOLDABLE-CONS{Nat, Nat} .
    protecting FUNCTION-ID{Bool} .
    protecting FUNCTION-ID{Nat} .
    protecting FUNCTION-COMP{Nat,Bool,Bool} .
    protecting FUNCTION-COMP{Nat,Nat,Bool} .
    protecting FUNCTION-COMP{Nat,Nat,Nat} .

    vars N M : Nat .

    op even : -> =>{Nat,Bool} .
    eq even 0       = true .
    eq even s(0)    = false .
    eq even s(s(N)) = even N .

    op odd : -> =>{Nat,Bool} .
    eq odd 0        = false .
    eq odd s(0)     = true .
    eq odd s(s(N))  = odd N .

    op double : -> =>{Nat,Nat} .
    eq double N = 2 * N .

    op aanndd : -> =>{Bool, =>{Bool,Bool}} .
    eq aanndd true true     = true .
    eq aanndd true false    = false .
    eq aanndd false true    = false .
    eq aanndd false false   = false .

    op + : -> =>{Nat, =>{Nat,Nat}} .
    eq + N M = N + M .

    --- some constants to play with
    op list1 : -> Cons{Nat} .
    eq list1 = 3 : 5 : 8 : 2 : 19 : 20 : [] .

    op list2 : -> Cons{Nat} .
    eq list2 = 16 : 100 : 0 : 3 : 9 : 19 : 22 : 101 : [] .
endfm
)

(reduce map even Nothing .)
(reduce map odd (Just 3) .)
(reduce map odd list1 .)
(reduce map even list2 . )
(reduce map (even . double) list1 . )
(reduce foldl aanndd true (map (id . even . id . double . id) list1) .)
(reduce foldl + 0 list1 .)
```