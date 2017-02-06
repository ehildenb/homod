Numbers
=======

This is the numbers hierarchy from the prelude flattened and trimmed down a bit.
We're just using it for the sort/subsort structure.

```maude
fmod NUMBERS is
  sorts Zero NzNat Nat .
  subsort Zero NzNat < Nat .

  sorts NzInt Int .
  subsorts NzNat < NzInt Nat < Int .

  sorts PosRat NzRat Rat .
  subsorts NzInt < NzRat Int < Rat .
  subsorts NzNat < PosRat < NzRat .

  op 0 : -> Zero [ctor] .

  op s_ : Nat -> NzNat [ctor iter] .

  op _+_ : NzNat Nat -> NzNat [assoc comm prec 33] .
  op _+_ : Nat Nat -> Nat [ditto] .

  op sd : Nat Nat -> Nat [comm] .

  op _*_ : NzNat NzNat -> NzNat [assoc comm prec 31] .
  op _*_ : Nat Nat -> Nat [ditto] .

  op -_ : NzNat -> NzInt [ctor] .
  op -_ : NzInt -> NzInt [ditto] .
  op -_ : Int -> Int [ditto] .

  op _+_ : Int Int -> Int [assoc comm prec 33] .
  op _-_ : Int Int -> Int [prec 33 gather (E e)] .

  op _*_ : NzInt NzInt -> NzInt [assoc comm prec 31] .
  op _*_ : Int Int -> Int [ditto] .

  op _/_ : NzInt NzNat -> NzRat [ctor prec 31 gather (E e)] .

  var I J : NzInt .
  var N M : NzNat .
  var K : Int .
  var Z : Nat .
  var Q : NzRat .
  var R : Rat .

  op _/_ : NzNat NzNat -> PosRat [ctor ditto] .
  op _/_ : PosRat PosRat -> PosRat [ditto] .
  op _/_ : NzRat NzRat -> NzRat [ditto] .
  op _/_ : Rat NzRat -> Rat [ditto] .
  eq 0 / Q = 0 .
  eq I / - N = - I / N .
  eq (I / N) / (J / M) = (I * M) / (J * N) .
  eq (I / N) / J = I / (J * N) .
  eq I / (J / M) = (I * M) / J .

  op -_ : NzRat -> NzRat [ditto] .
  op -_ : Rat -> Rat [ditto] .
  eq - (I / N) = - I / N .

  op _+_ : PosRat PosRat -> PosRat [ditto] .
  op _+_ : PosRat Nat -> PosRat [ditto] .
  op _+_ : Rat Rat -> Rat [ditto] .
  eq I / N + J / M = (I * M + J * N) / (N * M) .
  eq I / N + K = (I + K * N) / N .

  op _-_ : Rat Rat -> Rat [ditto] .
  eq I / N - J / M = (I * M - J * N) / (N * M) .
  eq I / N - K = (I - K * N) / N .
  eq K - J / M = (K * M - J ) / M .

  op _*_ : PosRat PosRat -> PosRat [ditto] .
  op _*_ : NzRat NzRat -> NzRat [ditto] .
  op _*_ : Rat Rat -> Rat [ditto] .
  eq Q * 0 = 0 .
  eq (I / N) * (J / M) = (I * J) / (N * M).
  eq (I / N) * K = (I * K) / N .
endfm
```

Sets in Maude
=============

To have a set data-structure in Maude, this is the necassary work. Note that we
want it to be the case that `Set{Nat} < Set{Int}`, which means we have to make
all those subsort declarations ourselves in the module `MY-MOD`.

```maude
fth TRIV is sort Elt . endfth

fmod SET{X :: TRIV} is
  sorts NeSet{X} Set{X} .
  subsort X$Elt < NeSet{X} < Set{X} .

  op mt  : -> Set{X} .

  op _,_ : NeSet{X} Set{X} -> NeSet{X} [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{X}   Set{X} -> Set{X}   [ctor ditto] .

  var N : NeSet{X} .
  eq N , N = N .
endfm

view Zero   from TRIV to NUMBERS is sort Elt to Zero   . endv
view NzNat  from TRIV to NUMBERS is sort Elt to NzNat  . endv
view Nat    from TRIV to NUMBERS is sort Elt to Nat    . endv
view NzInt  from TRIV to NUMBERS is sort Elt to NzInt  . endv
view Int    from TRIV to NUMBERS is sort Elt to Int    . endv
view PosRat from TRIV to NUMBERS is sort Elt to PosRat . endv
view NzRat  from TRIV to NUMBERS is sort Elt to NzRat  . endv
view Rat    from TRIV to NUMBERS is sort Elt to Rat    . endv

fmod MY-MOD is
  extending SET{Zero}   .
  extending SET{NzNat}  .
  extending SET{Nat}    .
  extending SET{NzInt}  .
  extending SET{Int}    .
  extending SET{PosRat} .
  extending SET{NzRat}  .
  extending SET{Rat}    .

  subsorts Set{Zero} Set{NzNat} < Set{Nat}             .
  subsorts Set{NzNat} < Set{NzInt} Set{Nat} < Set{Int} .
  subsorts Set{NzInt} < Set{NzRat} Set{Int} < Set{Rat} .
  subsorts Set{NzNat} < Set{PosRat} < Set{NzRat}       .

  subsort NeSet{Zero} NeSet{NzNat} < NeSet{Nat}                .
  subsorts NeSet{NzNat} < NeSet{NzInt} NeSet{Nat} < NeSet{Int} .
  subsorts NeSet{NzInt} < NeSet{NzRat} NeSet{Int} < NeSet{Rat} .
  subsorts NeSet{NzNat} < NeSet{PosRat} < NeSet{NzRat}         .

  subsort NeSet{Zero}   < Set{Zero}   .
  subsort NeSet{NzNat}  < Set{NzNat}  .
  subsort NeSet{Nat}    < Set{Nat}    .
  subsort NeSet{NzInt}  < Set{NzInt}  .
  subsort NeSet{Int}    < Set{Int}    .
  subsort NeSet{PosRat} < Set{PosRat} .
  subsort NeSet{NzRat}  < Set{NzRat}  .
  subsort NeSet{Rat}    < Set{Rat}    .
endfm
```

What we Actually Want
=====================

However, in the example above, we aren't actually getting quite what we might
hope for. It's a simple annoyance, namely that Maude spins up separate modules
for each instantiation `extending Set{X}`. This causes many (useless) warnings
about importing the operators `mt` and `_,_` from unrelated contexts. More
realistically (and what people end up doing in practice with Maude, eg. in the
prelude), what we want is the following flattened module:

```maude
fmod MY-MOD-2 is
  protecting NUMBERS .
 
  sorts NeSet{Zero}    Set{Zero}
        NeSet{NzNat}   Set{NzNat}
        NeSet{Nat}     Set{Nat}
        NeSet{NzInt}   Set{NzInt}
        NeSet{Int}     Set{Int}
        NeSet{PosRat}  Set{PosRat}
        NeSet{NzRat}   Set{NzRat}
        NeSet{Rat}     Set{Rat} .

  subsorts Set{Zero} Set{NzNat} < Set{Nat}  .
  subsorts Set{NzNat} < Set{NzInt} Set{Nat} < Set{Int} .
  subsorts Set{NzInt} < Set{NzRat} Set{Int} < Set{Rat} .
  subsorts Set{NzNat} < Set{PosRat} < Set{NzRat}       .

  subsort NeSet{Zero} NeSet{NzNat} < NeSet{Nat}                .
  subsorts NeSet{NzNat} < NeSet{NzInt} NeSet{Nat} < NeSet{Int} .
  subsorts NeSet{NzInt} < NeSet{NzRat} NeSet{Int} < NeSet{Rat} .
  subsorts NeSet{NzNat} < NeSet{PosRat} < NeSet{NzRat}         .

  subsort Zero   < NeSet{Zero}   < Set{Zero}   .
  subsort NzNat  < NeSet{NzNat}  < Set{NzNat}  .
  subsort Nat    < NeSet{Nat}    < Set{Nat}    .
  subsort NzInt  < NeSet{NzInt}  < Set{NzInt}  .
  subsort Int    < NeSet{Int}    < Set{Int}    .
  subsort PosRat < NeSet{PosRat} < Set{PosRat} .
  subsort NzRat  < NeSet{NzRat}  < Set{NzRat}  .
  subsort Rat    < NeSet{Rat}    < Set{Rat}    .

  op mt : -> Set{Zero}   [ctor] .
  op mt : -> Set{NzNat}  [ctor] .
  op mt : -> Set{Nat}    [ctor] .
  op mt : -> Set{NzInt}  [ctor] .
  op mt : -> Set{Int}    [ctor] .
  op mt : -> Set{PosRat} [ctor] .
  op mt : -> Set{NzRat}  [ctor] .
  op mt : -> Set{Rat}    [ctor] .

  op _,_ : Set{Zero}   Set{Zero}   -> Set{Zero}   [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{NzNat}  Set{NzNat}  -> Set{NzNat}  [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{Nat}    Set{Nat}    -> Set{Nat}    [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{NzInt}  Set{NzInt}  -> Set{NzInt}  [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{Int}    Set{Int}    -> Set{Int}    [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{PosRat} Set{PosRat} -> Set{PosRat} [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{NzRat}  Set{NzRat}  -> Set{NzRat}  [ctor assoc comm id: mt prec 99] .
  op _,_ : Set{Rat}    Set{Rat}    -> Set{Rat}    [ctor assoc comm id: mt prec 99] .

  op _,_ : NeSet{Zero}   Set{Zero}   -> NeSet{Zero}   [ctor ditto] .
  op _,_ : NeSet{NzNat}  Set{NzNat}  -> NeSet{NzNat}  [ctor ditto] .
  op _,_ : NeSet{Nat}    Set{Nat}    -> NeSet{Nat}    [ctor ditto] .
  op _,_ : NeSet{NzInt}  Set{NzInt}  -> NeSet{NzInt}  [ctor ditto] .
  op _,_ : NeSet{Int}    Set{Int}    -> NeSet{Int}    [ctor ditto] .
  op _,_ : NeSet{PosRat} Set{PosRat} -> NeSet{PosRat} [ctor ditto] .
  op _,_ : NeSet{NzRat}  Set{NzRat}  -> NeSet{NzRat}  [ctor ditto] .
  op _,_ : NeSet{Rat}    Set{Rat}    -> NeSet{Rat}    [ctor ditto] .

  var NeZero   : NeSet{Zero}   .
  var NeNzNat  : NeSet{NzNat}  .
  var NeNat    : NeSet{Nat}    .
  var NeNzInt  : NeSet{NzInt}  .
  var NeInt    : NeSet{Int}    .
  var NePosRat : NeSet{PosRat} .
  var NeNzRat  : NeSet{NzRat}  .
  var NeRat    : NeSet{Rat}    .

  eq NeZero   , NeZero   = NeZero   .
  eq NeNzNat  , NeNzNat  = NeNzNat  .
  eq NeNat    , NeNat    = NeNat    .
  eq NeNzInt  , NeNzInt  = NeNzInt  .
  eq NeInt    , NeInt    = NeInt    .
  eq NePosRat , NePosRat = NePosRat .
  eq NeNzRat  , NeNzRat  = NeNzRat  .
  eq NeRat    , NeRat    = NeRat    .
endfm
```

How to Get It?
==============

Think of this as a universal construction. For every part of a specified theory,
we want to guarantee the existence of another part. For example, for every sort
`X` in a theory, we want to guarantee that `Set{X}` and `NeSet{X}` exist.
Additionally, for every subsort `A < B`, we want to make sure that
`Set{A} < Set{B}` and `NeSet{A} < NeSet{B}`.

This universal module has a "commutative diagram" flavor, where certain parts of
the theory are called out as already existing (the `forall`), and as a result we
ensure that other parts exsit (the `exists`).

```
univ SET

  forall:
    sort A .
  exists:
    sorts NeSet{$A} Set{$A} .
    subsort $A < NeSet{$A} < Set{$A} .
    
    op mt  : -> Set{$A} .
    op _,_ : Set{$A}   Set{$A} -> Set{$A}   [ctor assoc comm id: mt prec 99] .
    op _,_ : NeSet{$A} Set{$A} -> NeSet{$A} [ctor ditto] .

    var NA : NeSet{$A} .
    eq NA , NA = NA .
   
  forall:
    sorts A B .
    subsort A < B .
  exists:
    subsort NeSet{$A} < NeSet{$B} .
    subsorts Set{$A} < Set{$B} .

  --- alternative to MAPPABLE-SET (below)
  --- lift each operator on sort A to work on sort Set{A}
  forall:
    sorts A B .
    op f : A -> B .
  exists:
    op $f : Set{$A} -> Set{$B} .

    var a : $A . vars NA NA' : NeSet{$A} .
    eq $f(mt)       = mt .
    eq $f(NA , NA') = $f(NA) , $f(NA') .

enduniv
```

Functions
---------

```
univ FUNCTION

  forall:
    sorts A B .
  exists:
    sort $A=>$B .
    op __ : $A=>$B $A -> [$B] .

  forall:
    sort A .
  exists:
    op id : -> $A=>$A .
    var a : $A .
    eq id a = a .
    
  --- lambda abstraction
  forall:
    sorts A B .
    op f : A -> B .
  exists:
    sort Var{$A} .
    op $f : -> $A=>$B .
    var A : $A .
    eq $f A = $f(A) .

  forall:
    sorts A B C .
    subsort A < B .
  exists:
    subsort $C=>$A < $C=>$B .
    subsort $B=>$C < $A=>$C .

  forall:
    sorts A B C .
  exists:
    op _._ : $B=>$C $A=>$B -> $A=>$C .
    var f : $B=>$C . var g : $A=>$B . var A : $A .
    eq id . g = g . eq f . id = f .
    eq (f . g) A = f(g(A)) .

enduniv
```

Mappable Sets
-------------

Here we define an explicit `map` function for sets instead of generating an
implicit operator over sets for ever operator over the base sorts.

```
univ MAPPABLE-SET
  extends SET .
  extends FUNCTION .

  forall:
    sorts A B .
  exists:
    op map__ : $A=>$B Set{$A} -> Set{$B} .

    var f : $A=>$B . var A : $A . vars NA NA' : NeSet{$A} .

    eq map f A          = f A .
    eq map f mt         = mt .
    eq map f (NA , NA') = map f NA , map f NA' .

enduniv
```
