---
author: Everett Hildenbrandt, Lucas Pena
title: Generating Higher-order Maude from Haskell
format: latex
geometry: margin=2.0cm
execute: maude-gen.maude haskell-orig.hs
...


Introduction
============

TODO: Say stuff about paper (Tannen), say stuff about "people like Haskell". Say
stuff about eqnl logic having HO power.

Original Haskell
================

### Data Declarations (with ADTs)

```haskell{exec:haskell-orig.hs}
module HaskTest where

import Prelude hiding (Foldable, Maybe, map, Just, Nothing, foldl)

data Maybe a = Just a
             | Nothing
             deriving Show

infixr 5 :|
data Cons a = Nil
            | a :| Cons a
            deriving Show
```

### Type Classes

```haskell{exec:haskell-orig.hs}
class Mappable f where
    map :: (a -> b) -> f a -> f b

instance Mappable Maybe where
    map f Nothing = Nothing
    map f (Just a) = Just (f a)

instance Mappable Cons where
    map f Nil = Nil
    map f (a :| as) = (f a) :| map f as

class Foldable f where
    foldl :: (b -> a -> b) -> b -> f a -> b

instance Foldable Cons where
    foldl f b Nil = b
    foldl f b (a :| as) = foldl f (f b a) as

--endmodule
```

Above is an example of two common Haskell algebraic datatypes, the `Maybe`
datatype specifying the possible absence of data, as well as the `Cons` datatype
representing a list. In addition, the typeclasses `Mappable` and `Foldable` are
defined, along with instances `map` and `foldl` of those typeclasses using the
`Maybe` and `Cons` datatypes. Note that both `map` and `foldl` above are higher
order functions, something not explicitly available in Maude. We would like to
be able to use Haskell-like higher order code within Maude, or even be able to
use the above code directly in Maude. The following sections discuss how this
and similar higher order Haskell modules can be converted into equivalent Maude
modules.


Maude Code
==========

Pre-Exists
----------

```maude{exec:maude-gen.maude}
fmod FUNCTION{X :: TRIV, Y :: TRIV} is
    sort =>{X,Y} .
    op __   : =>{X,Y} X$Elt -> Y$Elt .
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

The above code is boilerplate that will automatically be generated for any
Haskell module. The most important of the three modules specified above is the
`FUNCTION` module, parametrized on two sorts `X` and \texttt{Y}. With these
sorts, it creates a new sort that represents a function from `X` to `Y`. In this
fashion, we are able to simulate higher order functions in Maude from `X` to
`Y`, provided that both `X` and `Y` have views to `TRIV`. We will see more
examples of this later. Additionally, the `__` operator is used for function
application, as it requires a function from `X` to `Y` and an element in `X` and
returns an element in `Y`. By defining the `__` operator in this way, we also
are able to rely on Maude's sort checker to rule out ill-formed programs.

The other modules are specified mostly for the user's convenience. The
`FUNCTION-ID` module gives the identity function on `X`. The `FUNCTION-COMP`
module is parametrized on `X`, `Y`, and `Z`, and allows one to compose a
function from `Y` to `Z` with a function from `X` to `Y`, resulting in a
function from `X` to `Z`. Here, using the `=>{.,.}` notation, higher order
function composition can be expressed without much difficulty. Further, note
that by our definition of `_._`, if two functions cannot be composed, Maude's
sort checker will disallow usage of the `_._` operator.

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
    op Nil : -> Cons{a} .
    op _:|_ : a$Elt Cons{a} -> Cons{a} .
endfm
```

TODO: These are just ADTs, so these are super easy to translate (because the
models of eqnl logic are algebras). This is $\epsilon$-representation distance,
so it's actually not that useful to provide these definitions in Haskell.

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
```

TODO: These are parameterized views - they allow automatic creation of the
correct function sorts (which removes a lot of boilerplate). Now the user can
just say which function sorts they want, and the correct view to `TRIV` will be
generated for them.

```maude{exec:maude-gen.maude}
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
    eq map f Nil = Nil .
    eq map f (a :| as) = f a :| map f as .
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

    eq foldl f b Nil = b .
    eq foldl f b (a :| as) = foldl f (f b a) as .
endfm
)
```

TODO: These are the instances from above. Notice that for the "higher-order"
functionality, we have provided combinators which just place the correct
constants (which have correct associated function sorts) in the correct places.
The definitions are exactly the same (nearly copy paste). Partial application is
immediately supported because of the `=>{ , }` view and the `__` operator. For
instance if `+ : -> =>{Nat, =>{Nat, Nat}}`, we

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
    eq list1 = 3 :| 5 :| 8 :| 2 :| 19 :| 20 :| Nil .

    op list2 : -> Cons{Nat} .
    eq list2 = 16 :| 100 :| 0 :| 3 :| 9 :| 19 :| 22 :| 101 :| Nil .
endfm
)
```

TODO: Talk about defn of `aanndd`, `+` and `double`, notably how how `+` and
`double` are defined in terms of their algebraic counterparts, but `aanndd` is
defined more functionally (though we are using algebra here, but the point is
that that code could be copy-pasted from Haskell code).

```maude{exec:maude-gen.maude}
--- map over Maybe type
(reduce map even Nothing .)
(reduce map odd (Just 3) .)

--- map over Cons type
(reduce map odd list1 .)
(reduce map even list2 . )

--- function composition
(reduce map (even . double) list1 . )

--- foldl over Cons type and function composition
(reduce foldl aanndd true (map (id . even . id . double . id) list1) .)

--- foldl numeric over Cons type
(reduce foldl + 0 list1 .)

--- map partially applied function over Cons type
(reduce map (+ 3) list1 .)
```

TODO: Talk about different things going on here. Make sure to mention
partial application happening in the last example. Also make note of the problem
we face when the sort to infer is ambiguous.

### Output

```maude
reduce in TESTING :
  (map).=>{=>{Nat,Bool},=>{Maybe{Nat},Maybe{Bool}}}even(Nothing).Maybe{Nat}
result Maybe{Bool} :
  (Nothing).Maybe{Bool}

reduce in TESTING :
  (map).=>{=>{Nat,Bool},=>{Maybe{Nat},Maybe{Bool}}}odd Just 3
result Maybe{Bool} :
  Just true

reduce in TESTING :
  (map).=>{=>{Nat,Bool},=>{Cons{Nat},Cons{Bool}}}odd list1
result Cons{Bool} :
  true :| true :| false :| false :| true :| false :|(Nil).Cons{Bool}

reduce in TESTING :
  (map).=>{=>{Nat,Bool},=>{Cons{Nat},Cons{Bool}}}even list2
result Cons{Bool} :
  true :| true :| true :| false :| false :| false :| true :| false :|(Nil).Cons{Bool}

reduce in TESTING :
  (map).=>{=>{Nat,Bool},=>{Cons{Nat},Cons{Bool}}}(even . double)list1
result Cons{Bool} :
  true :| true :| true :| true :| true :| true :|(Nil).Cons{Bool}

reduce in TESTING :
  (foldl).=>{=>{Bool,=>{Bool,Bool}},=>{Bool,=>{Cons{Bool},Bool}}}aanndd true(map).=>{=>{Nat,Bool},=>{Cons{Nat},Cons{
    Bool}}}((id).=>{Bool,Bool}. even .(id).=>{Nat,Nat}. double .(id).=>{Nat,Nat})list1
result Bool :
  true

reduce in TESTING :
  (foldl).=>{=>{Nat,=>{Nat,Nat}},=>{Nat,=>{Cons{Nat},Nat}}}+ 0 list1
result NzNat :
  57

reduce in TESTING :
  (map).=>{=>{Nat,Nat},=>{Cons{Nat},Cons{Nat}}}+ 3 list1
result Cons{Nat} :
  6 :| 8 :| 11 :| 5 :| 22 :| 23 :|(Nil).Cons{Nat}
```


Future Work
===========

TODO: Actually generate the Maude code using a Full Maude parser.

TODO: Lambda abstraction would be cool (we could place passed in terms in the
correct spot inside the algebra). We can use one of the `LAMBDA2CL` compilers to
help with this (automate the process). We would have to do type inference so we
know which modules to import. We could also think about adding other "nice"
things which most people associate with functional programming (eg. the Haskell
`Prelude`).

TODO: More general partial application/sort inference.

