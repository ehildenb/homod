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
fmod SORT-POSETS is
    protecting QID * (sort Qid to Sort) .
    protecting BOOL .

    sorts SortSet NeSortSet .
    subsort Sort < NeSortSet < SortSet .
    sorts NeSortPoset SortPoset .
    subsorts NeSortSet < NeSortPoset < SortPoset .
    subsort SortSet < SortPoset .
    sorts NeSortPosets SortPosets .
    subsort NeSortPosets < SortPosets .

    vars X X' X'' : Sort .
    vars XS XS' : SortSet . vars NXS NXS' : NeSortSet .
    vars XPS XPS' : SortPoset . vars NXPS NXPS' : NeSortPoset .
    var XPSS : SortPosets . vars NXPSS NXPSS' : NeSortPosets .

    op none : -> SortSet [ctor] .
    op _;_ : SortSet SortSet -> SortSet [ctor assoc comm id: none] .
    op _;_ : NeSortSet SortSet -> NeSortSet [ctor assoc comm id: none] .
    --------------------------------------------------------------------
    eq X ; X = X .

    op _;_ : SortPoset SortPoset -> SortPoset [ctor ditto] .
    op _;_ : NeSortPoset SortPoset -> NeSortPoset [ctor ditto] .
    op _>[_] : Sort SortSet -> NeSortPoset [ctor right id: none prec 40] .
    ----------------------------------------------------------------------
    eq X > [XS] ; X > [XS'] = X > [XS ; XS'] .

    op _in_ : Sort SortPoset -> Bool .
    ----------------------------------
    eq X in (X > [XS] ; XPS) = true .
    eq X in (X' > [X ; XS'] ; XPS) = true .
    eq X in XPS = false [owise] .

    op {_} : SortPoset -> SortPosets [ctor] .
    op {_} : NeSortPoset -> NeSortPosets [ctor] .
    ---------------------------------------------
    ceq { X > [X' ; XS] ; XPS } = { X > [X' ; XS] ; X' ; XPS } if X =/= X' /\ not (X' in XPS) .

    op .SortPosets : -> SortPosets [ctor] .
    op _;_ : SortPosets SortPosets -> SortPosets [ctor assoc comm id: .SortPosets prec 60 format(d n s d)] .
    op _;_ : NeSortPosets SortPosets -> NeSortPosets [ctor assoc comm id: .SortPosets prec 60 format(d n s d)] .
    ------------------------------------------------------------------------------------------------------------
    eq { none } = .SortPosets .
    eq { X > [XS] ; XPS } ; { X > [XS'] ; XPS' } = { X > [XS ; XS'] ; XPS ; XPS' } .

    op _[_] : SortPosets Sort -> SortPoset .
    ----------------------------------------
    eq ({ X > [XS] ; XPS } ; XPSS)[X] = X > [XS] ; XPS .
    eq XPSS[X] = none [owise] .

---    op sortPosets : Module -> SortPosets .
---    op sortPosets : SortSet SubsortDeclSet -> SortPosets .
---    ------------------------------------------------------
---    eq sortPosets( M ) = sortPosets(getSorts(M), getSubsorts(M)) .
---    eq sortPosets( none , none ) = .SortPosets .
---    eq sortPosets( X ; XS , SS ) = {X} ; sortPosets(XS , SS) .
---    eq sortPosets( XS , subsort X' < X . SS ) = {X > [X']} ; sortPosets(XS, SS) .

    op sortSet : SortPoset -> SortSet .
    op sortSet : SortPosets -> SortSet .
    ------------------------------------
    eq sortSet( none ) = none .
    eq sortSet( X > [XS] ) = X ; XS .
    eq sortSet( NXPS ; NXPS' ) = sortSet(NXPS) ; sortSet(NXPS') .
    eq sortSet( .SortPosets ) = none .
    eq sortSet( { NXPS } ) = sortSet(NXPS) .
    eq sortSet( NXPSS ; NXPSS' ) = sortSet(NXPSS) ; sortSet(NXPSS') .

---    op subsortSet : SortPoset -> SubsortDeclSet .
---    op subsortSet : SortPosets -> SubsortDeclSet .
---    ----------------------------------------------
---    eq subsortSet( none ) = none .
---    eq subsortSet( X ) = none .
---    eq subsortSet( X > [X' ; XS] ) = subsort X' < X . subsortSet(X > [XS]) .
---    eq subsortSet( NXPS ; NXPS' ) = subsortSet(NXPS) subsortSet(NXPS') .
---    eq subsortSet( .SortPosets ) = none .
---    eq subsortSet( { NXPS } ) = subsortSet(NXPS) .
---    eq subsortSet( NXPSS ; NXPSS' ) = subsortSet(NXPSS) subsortSet(NXPSS') .
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
    extending SORT-POSETS .

    vars X X' : Sort .
    vars XS XS' : SortSet . vars NXS NXS' NYS NYS' : NeSortSet .
    vars XPS XPS' : SortPoset . vars NXPS NXPS' NYPS NYPS' : NeSortPoset .
    vars XPSS XPSS' : SortPosets . vars NXPSS NXPSS' NYPSS NYPSS' : NeSortPosets .

    op _×_ : Sort Sort -> Sort [ctor assoc prec 30] .
    -------------------------------------------------
    op cross : SortSet SortSet -> SortSet [assoc] .
    op cross : SortPoset SortPoset -> SortPoset [assoc] .
    op cross : SortPosets SortPosets -> SortPosets [assoc] .
    --------------------------------------------------------
    eq cross(NXS, none)          = none .
    eq cross(none, NXS')         = none .
    eq cross(NXPS, none)         = none .
    eq cross(none, NXPS')        = none .
    eq cross(XPSS, .SortPosets)  = .SortPosets .
    eq cross(.SortPosets, XPSS') = .SortPosets .
    --------------------------------------------
    eq cross(NXS ; NXS', NYS)       = cross(NXS, NYS) ; cross(NXS', NYS) .
    eq cross(NXS, NYS ; NYS')       = cross(NXS, NYS) ; cross(NXS, NYS') .
    eq cross(NXPS ; NXPS', NYPS)    = cross(NXPS, NYPS) ; cross(NXPS', NYPS) .
    eq cross(NXPS, NYPS ; NYPS')    = cross(NXPS, NYPS) ; cross(NXPS, NYPS') .
    eq cross(NXPSS ; NXPSS', NYPSS) = cross(NXPSS, NYPSS) ; cross(NXPSS', NYPSS) .
    eq cross(NXPSS, NYPSS ; NYPSS') = cross(NXPSS, NYPSS) ; cross(NXPSS, NYPSS') .
    ------------------------------------------------------------------------------
    eq cross(X > [XS], X' > [XS']) = (X × X') > [cross(X, XS') ; cross(XS, X')] .
    eq cross({XPS}, {XPS'}) = {cross(XPS, XPS')} .
endfm
```

Direct Sum
----------

```maude
fmod TESTING is
    protecting SORT-CARTESIAN-PRODUCT .

    op sorts1 : -> SortPosets .
    ---------------------------
    eq sorts1 =   { 'String > ['Char] }
                ; { 'Rat > ['Int] ; 'Int > ['Nat ; 'Neg] ; 'Nat > ['Pos ; 'Zero] }
                .

endfm

fmod DATA-MODULE is
    --- extending META-MODULE .
    extending SORT-POSETS .

    sort DataExp DataModule DataModules .
    subsort DataModule < DataModules .
    subsort String < DataExp < Sort .

    op co     : Sort -> DataExp .
    op contra : Sort -> DataExp .
    op __ : DataExp DataExp -> DataExp [assoc prec 33] .

    op data_is_enddata : DataExp SortPosets -> DataModule [ctor format (n d s n++i n--i d)] .

    op none : -> DataModules [ctor] .
    op __ : DataModules DataModules -> DataModules
            [ctor assoc comm id: none prec 90 format(n n n)] .

endfm
```

Sort Modules
============

```maude

reduce "List{" co('S) "}" .

reduce

data "List{" co('S) "}" is
    { "List{" co('S) "}" > [co('S)]
    }
enddata

data contra('X) "=>" co('Y) is
    { none
    }
enddata

.

q
```
