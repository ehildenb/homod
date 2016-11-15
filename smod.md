
Sort Modules
============

The goal of this file is to allow defining more complex sort structures as
transformations on existing sort structures. To do so, it defines a few basic
operations on the sort POSET.

To Poset
--------

The `META-MODULE` stores sorts in a flat way (as a list of sorts and the list of
edges in the sort POSET). This module provides functionality for taking a Maude
module and getting the connected components of the module in a non-flat way.

```maude
fmod SORT-CONNECTED-COMPONENTS is
    extending META-MODULE .
    protecting BOOL .

    sorts SortPoset SortPosets .
    subsort SortPoset < SortPosets .
    sort SortCC SortCCs .
    subsort SortCC < SortCCs .

    vars X Y : Sort . vars XS XS' : SortSet . var SS : SubsortDeclSet .
    vars PXS PXS' : SortPosets . var M : Module .

    op _>[_] : Sort SortSet -> SortPoset [ctor prec 40] .
    op .SortPosets : -> SortPosets [ctor] .
    op __ : SortPosets SortPosets -> SortPosets [ctor assoc comm id: .SortPosets prec 50 format(d ni d)] .
    ------------------------------------------------------------------------------------------------------
    eq X > [ none ] = .SortPosets .
    eq X > [XS] X > [XS'] = X > [XS ; XS'] .

    op {_|_} : SortSet SortPosets -> SortCC [ctor prec 52 format(n s d n+i n-i d)] .
    op .SortCCs : -> SortCCs [ctor] .
    op __ : SortCCs SortCCs -> SortCCs [ctor assoc comm id: .SortCCs prec 60] .
    ---------------------------------------------------------------------------
    eq { X ; XS | PXS } { X ; XS' | PXS' } = { X ; XS ; XS' | PXS PXS' } .

    op sortCCs : SortSet -> SortCCs .
    ---------------------------------
    eq sortCCs( none ) = .SortCCs .
    eq sortCCs( X ; XS ) = { X | .SortPosets } sortCCs(XS) .

    op subsortCCs : SubsortDeclSet -> SortCCs .
    -------------------------------------------
    eq subsortCCs( none ) = .SortCCs .
    eq subsortCCs( subsort X < Y . SS ) = { X ; Y | Y > [X] } subsortCCs(SS) .

    op subsorts : Sort SortPosets -> SortSet .
    ------------------------------------------
    eq subsorts( X , X > [XS'] PXS ) = XS' .
    eq subsorts( X , PXS ) = none [owise] .

    op sortConnectedComponents : Module -> SortCCs .
    ------------------------------------------------
    eq sortConnectedComponents(M) = sortCCs(getSorts(M)) subsortCCs(getSubsorts(M)) .
endfm
```


Constructions
=============

Cartesian Product
-----------------

We would like to take the cartesian product of two connected components. This
does that by taking the cartesian product of the posets.

```maude
fmod SORT-CARTESIAN-PRODUCT is
    extending SORT-CONNECTED-COMPONENTS .

    vars X Y : Sort . vars XS XS' YS YS' ZS : SortSet .
    vars PXS PYS : SortPosets . var SCCS : SortCCs .

    op _×_ : Sort Sort -> Sort [ctor prec 30] .
    op _ × {_} : Sort SortSet -> SortSet .
    op {_} × _ : SortSet Sort -> SortSet .
    op {_} × {_} : SortSet SortSet -> SortSet .
    -------------------------------------------
    eq { none } × { YS } = none .
    eq { X ; XS } × { YS } = X × { YS } ; { XS } × { YS } .
    eq X × { none } = none .
    eq X × { Y ; YS }  = X × Y ; X × { YS } .
    eq { none } × Y = none .
    eq { X ; XS } ×  Y  = X × Y ; { XS } × Y .

    op {_|_|_} : SortPosets SortSet SortPosets -> SortCCs .
    -------------------------------------------------------
    eq { PXS | none | PYS } = .SortCCs .
    ceq { PXS | X × Y ; ZS | PYS }
      = { { X ; XS } × { Y ; YS } | (X × Y) > [ X × { YS } ; { XS } × Y ] } { PXS | ZS | PYS }
        if XS := subsorts(X, PXS)
        /\ YS := subsorts(Y, PYS) .

    op _[_] : SortCCs Sort -> SortCCs .
    op _@[_,_] : SortCCs Sort Sort -> SortCC .
    ------------------------------------------
    eq ({X ; XS | PXS} SCCS)[X] = {X ; XS | PXS} .
    ceq SCCS @ [X,Y] = { PXS | {XS} × {YS} | PYS }
        if { XS | PXS } := SCCS [X]
        /\ { YS | PYS } := SCCS [Y] .
endfm
```


```maude
fmod TESTING is
    protecting SORT-CARTESIAN-PRODUCT .

    op initSubSorts : -> SubsortDeclSet .
    eq initSubSorts = ( subsort 'Int < 'Rat .
                        subsort 'Nat < 'Int .
                        subsort 'Pos < 'Nat .
                        subsort 'Neg < 'Int .
                        subsort 'Char < 'String .
                        subsort 'String < 'StringSet .
                        subsort 'String < 'StringList .
                      ) .

    op initSorts : -> SortSet .
    eq initSorts = ( 'Int ; 'Rat ; 'MySort1 ; 'MySort2 ) .

    op simpSorts1 : -> SortCC .
    op simpSorts2 : -> SortCC .
    ---------------------------
    eq simpSorts1 = subsortCCs( subsort 'B < 'A . subsort 'C < 'A . ) .
    eq simpSorts2 = subsortCCs( subsort 'F < 'D . subsort 'E < 'D . ) .
endfm

reduce simpSorts1 simpSorts2 .
reduce (simpSorts1 simpSorts2)@['A, 'C] .

```
