
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
    subsorts SortSet < SortPoset .

    vars X X' X'' : Sort . vars XS XS' : SortSet . vars XPS XPS' : SortPoset .

    op _;_ : SortPoset SortPoset -> SortPoset [ctor ditto] .
    op _>[_] : Sort SortSet -> SortPoset [ctor right id: none prec 40] .
    --------------------------------------------------------------------
    eq X > [XS] ; X > [XS'] = X > [XS ; XS'] .

    op {_} : SortPoset -> SortPosets [ctor] .
    op _ in _ : SortSet SortPosets -> Bool .
    ----------------------------------------
    eq X in { X > [XS] ; XPS } = true .
    eq X in { X' > [X ; XS'] ; XPS } = true .
    eq X in { XPS } = false [owise] .
    eq (X ; XS) in { XPS } = X in { XPS } and XS in { XPS } .
    ceq { X > [X' ; XS] ; XPS } = { X > [X' ; XS] ; X' ; XPS }
        if not (X == X') /\ not (X' in XPS) .

    op .SortPosets : -> SortPosets [ctor] .
    op _;_ : SortPosets SortPosets -> SortPosets [ctor assoc comm id: .SortPosets prec 60] .
    ----------------------------------------------------------------------------------------
    eq { none } = .SortPosets .
    eq { X > [XS] ; XPS } ; { X > [XS'] ; XPS' } = { X > [XS ; XS'] ; XPS ; XPS' } .
endfm
```


    op {_} : SortPosets -> SortCC [ctor prec 52 format(n s+i n-i d)] .
    op .SortCCs : -> SortCCs [ctor] .
    op _;_ : SortCCs SortCCs -> SortCCs [ctor assoc comm id: .SortCCs prec 60] .
    ----------------------------------------------------------------------------
    eq { .SortPosets } = .SortCCs .
    eq { X > [XS] ; XPSS } ; { X > [XS'] ; YPSS } = { X > [XS ; XS'] ; XPSS ; YPSS } .

    op sortCCs : SortSet -> SortCCs .
    ---------------------------------
    eq sortCCs( none ) = .SortCCs .
    eq sortCCs( X ; XS ) = { X > [ none ] } ; sortCCs(XS) .

    op subsortCCs : SubsortDeclSet -> SortCCs .
    -------------------------------------------
    eq subsortCCs( none ) = .SortCCs .
    eq subsortCCs( subsort X < Y . SS ) = { Y > [X] } ; subsortCCs(SS) .

    op subsorts : Sort SortPosets -> SortSet .
    ------------------------------------------
    eq subsorts( X , X > [XS] ; XPSS ) = XS ; subsorts(X, XPSS) .
    eq subsorts( X , XPSS ) = none [owise] .

    op sortConnectedComponents : Module -> SortCCs .
    ------------------------------------------------
    eq sortConnectedComponents(M) = sortCCs(getSorts(M)) ; subsortCCs(getSubsorts(M)) .

    op asSortSet : SortCCs -> SortSet .
    -----------------------------------
    eq asSortSet( .SortCCs ) = none .
    eq asSortSet( { X > [XS] ; XPSS } ; SCCS ) = X ; XS ; asSortSet({XPSS} ; SCCS) .

    op asSubsortDeclSet : SortCCs -> SubsortDeclSet .
    -------------------------------------------------
    eq asSubsortDeclSet( .SortCCs  ) = none .
    eq asSubsortDeclSet( { X > [ none ] ; XPSS } ; SCCS )
     = asSubsortDeclSet( {                XPSS } ; SCCS ) .
    eq asSubsortDeclSet( { X > [ X' ; XS ] ; XPSS } ; SCCS )
     = asSubsortDeclSet( { X > [      XS ] ; XPSS } ; SCCS ) subsort X' < X . .
endfm


Constructions
=============

Cartesian Product
-----------------

We would like to take the cartesian product of two connected components. This
does that by taking the cartesian product of the posets.

```
fmod SORT-CARTESIAN-PRODUCT is
    extending SORT-CONNECTED-COMPONENTS .

    vars X Y : Sort . vars XS XS' YS YS' ZS : SortSet .
    vars PXS PYS : SortPosets . var SCCS : SortCCs .
    vars XPS YPS : SortPoset . vars XPSS YPSS : SortPosets .

    op _ × _ : Sort Sort -> Sort [ctor assoc prec 30] .
    op _ × _ : Sort SortSet -> SortSet .
    op _ × _ : SortSet Sort -> SortSet .
    op _ × _ : SortSet SortSet -> SortSet .
    -------------------------------------------
    eq none × YS = none .
    eq XS × none = none .
    eq (X ; XS) × YS = X × YS ; XS × YS .
    eq XS × (Y ; YS) = XS × Y ; XS × YS .
    eq (X ; XS) × Y = X × Y ; XS × Y .

---    op {_|_|_} : SortPosets SortSet SortPosets -> SortCCs .
---    -------------------------------------------------------
---    eq { PXS | none | PYS } = .SortCCs .
---    ceq { PXS | X × Y ; ZS | PYS }
---      = { { X ; XS } × { Y ; YS } | (X × Y) > [ X × { YS } ; { XS } × Y ] } { PXS | ZS | PYS }
---        if XS := subsorts(X, PXS)
---        /\ YS := subsorts(Y, PYS) .

    op _[_] : SortCCs Sort -> SortCC .
    ----------------------------------
    eq ({ X > [XS] ; XPSS } ; SCCS)[X] = { X > [XS] ; XPSS } .

    op _ × _ : SortPoset SortPoset -> SortPoset .
    op _ × _ : SortPosets SortPoset -> SortPosets .
    op _ × _ : SortPoset SortPosets -> SortPosets .
    op _ × _ : SortPosets SortPosets -> SortPosets .
    ------------------------------------------------
    eq X > [XS] × Y > [YS] = (X × Y) > [XS × Y ; X × YS] .
    eq (XPS ; XPSS) × YPSS = (XPS × YPSS) ; (XPSS × YPSS) .
    eq .SortPosets × YPS = .SortPosets .
    eq XPS × .SortPosets = .SortPosets .
    eq { XPS ; XPSS } × YPS = XPS × YPS ; {XPSS} × YPS .
    eq XPS × { YPS ; YPSS }  = XPS × YPS ; XPS × {YPSS} .

    op _ × _ : SortCC SortCC -> SortCC .
    op _ × _ : SortCC SortPoset -> SortCC .
    op _ × _ : SortPoset SortCC -> SortCC .
    op _ × _ : SortPoset SortPoset -> SortPoset .
    ---------------------------------------------
endfm
```


```
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

    var TS : SortCCs .

    op triangle1 : -> SortCC .
    op triangle2 : -> SortCC .
    op triangle1×triangle2 : -> SortCC .
    --------------------------------------
    eq triangle1 = subsortCCs( subsort 'B < 'A . subsort 'C < 'A . ) .
    eq triangle2 = subsortCCs( subsort 'E < 'D . subsort 'F < 'D . ) .
    ceq triangle1×triangle2 = TS['A] × TS['C]
        if TS := {triangle1 ; triangle2} .
endfm

reduce triangle1 .
reduce triangle2 .
reduce triangle1 .

```
