---
title: Narrowing Modulo SMT
author: Everett Hildenbrandt
geomety: margin=2.5cm
---

In this file, Narrowing modulo SMT is developed for the Maude language. A simple
imperative strategy language is given, which controls meta-level operations over
the set of states. A trace which records the set of states seen up to each step
as well as the states first seen at each step is kept.

Constrained Terms
=================

First we need to be able to manipulate constrained symbolic terms. Notable, we
need to be able to effectively compute term union and difference relative to a
given module.

```{.maude .meta-strategy}
fmod CTERM-SET is
  extending BOOL .
  protecting META-LEVEL .

  sorts CTerm NeCTermSet CTermSet CTermSet? .
  subsorts Term < CTerm < NeCTermSet < CTermSet < CTermSet? .

  var N : Nat . vars B B' B'' : Bool .
  var MOD : Module . var SUBST : Substitution .
  vars T T' : Term . vars CT CT' CT'' : CTerm .
  vars CTS CTS' : CTermSet . vars NeCTS NeCTS' : NeCTermSet .

  op _|_ : Term Bool -> CTerm [right id: true prec 52] .
  ------------------------------------------------------

  op .CTermSet : -> CTermSet .
  op _;;_ : CTermSet CTermSet   -> CTermSet   [ctor assoc comm id: .CTermSet prec 60] .
  op _;;_ : CTermSet CTermSet?  -> CTermSet?  [ctor ditto] .
  op _;;_ : CTermSet NeCTermSet -> NeCTermSet [ctor ditto] .
  ----------------------------------------------------------
  eq NeCTS ;; NeCTS = NeCTS .

  op _[_] : CTermSet? Module -> [CTermSet] [prec 64] .
  ----------------------------------------------------
  eq CT [ MOD ] = CT .

  op _++_ : CTermSet? CTermSet? -> CTermSet? [assoc comm id: .CTermSet prec 61] .
  -------------------------------------------------------------------------------
  ceq (T | B ;; CTS ++ CT' ;; CTS') [ MOD ] = (T | B'' ;; CTS ++ CTS') [ MOD ] if T' | B' := #varsApart(CT', T | B)
                                                                               /\ SUBST   := #subsumesWith(MOD, T, T')
                                                                               /\ B''     := #simplifyBool(B or (#substAsConstraint(SUBST) and #applySubstBool(SUBST, B'))) .
  eq  (NeCTS ++ NeCTS') [ MOD ] = NeCTS ;; NeCTS' [owise] .

  op _--_ : CTermSet? CTermSet? -> CTermSet? [right id: .CTermSet prec 62] .
  --------------------------------------------------------------------------
  eq  (.CTermSet -- NeCTS)    [ MOD ] = .CTermSet .
  eq  (CT ;; NeCTS -- NeCTS') [ MOD ] = (CT -- NeCTS') ++ (NeCTS -- NeCTS') [ MOD ] .
  ceq (CT    -- CT' ;; CTS)   [ MOD ] = .CTermSet if SUBST := #subsumesWith(MOD, CT', #varsApart(CT, CT')) .
  ceq (T | B -- CT' ;; CTS)   [ MOD ] = T | B'' -- CTS [ MOD ] if T' | B' := #varsApart(CT', T | B)
                                                               /\ SUBST   := #subsumesWith(MOD, T, T')
                                                               /\ B''     := #simplifyBool(B and (#substAsConstraint(SUBST) implies #applySubstBool(SUBST, not B))) .
  eq  (CT -- CT' ;; CTS) [ MOD ] = (CT -- (#intersect(CT, CT') [ MOD ])) -- CTS [ MOD ] [owise] .

  op #intersect : CTerm CTerm -> CTermSet? [comm] .
  -------------------------------------------------
  --- eq #intersect(T | B, T' | B') = 

  op #varsApart : CTerm CTerm -> CTerm .
  --------------------------------------

  op #applySubstBool : Substitution Bool -> Bool .
  ------------------------------------------------

  op #substAsConstraint : Substitution -> Bool .
  ----------------------------------------------

  --- TODO: Can this return multiple ways the terms match?
  op #subsumesWith : Module CTerm CTerm -> Substitution? .
  --------------------------------------------------------

  op #simplifyBool : Bool -> Bool .
  ---------------------------------
endfm
```

Analysis
========

`Analysis` is an $AC$-soup of state.

```{.maude .meta-strategy}
fmod ANALYSIS is
  sort Analysis .

  op .Analysis : -> Analysis .
  op __        : Analysis Analysis -> Analysis [assoc comm id: .Analysis prec 95 format(d n d)] .
  -----------------------------------------------------------------------------------------------
endfm
```

Current Module
--------------

Many parts need the analysis need the current module we're working in.

```{.maude .meta-strategy}
fmod MODULE is
  protecting META-LEVEL .
  extending ANALYSIS .

  sorts Command{=>Module} .

  var H : Header . var MOD : Module .

  op current-module <_> : Module -> Analysis .
  --------------------------------------------

  op set-module : Header -> Command{=>Module} .

  op _[_] : Command{=>Module} Module -> [Module] .
  ------------------------------------------------
  eq set-module(H) [ MOD ] = upModule(H, true) .
endfm
```

Current State
-------------

The current state (over which we will call commands like `metaReduce` and
`metaNarrow`) is also useful to have around. It consists of a set of state,
given by the sort `CTermSet`.

```{.maude .meta-strategy}
fmod STATE is
  protecting MODULE .
  protecting CTERM-SET .

  sorts Command{Module=>State} Command{=>State} .

  var N : Nat . var CS : Command{=>State} .
  vars T T' T'' : CTerm . vars NeCTS NeCTS' : NeCTermSet . vars CTS CTS' : CTermSet .
  var MOD : Module . var TYPE : Type . var SUBST : Substitution .

  op state <_> : CTermSet -> Analysis .
  -------------------------------------

  op _<_> : Command{Module=>State} Module -> Command{=>State} .
  op _[_] : Command{=>State} CTermSet -> [CTermSet] [prec 55] .
  -------------------------------------------------------------
  eq CS [ .CTermSet       ] = .CTermSet .
  eq CS [ NeCTS ;; NeCTS' ] = CS [ NeCTS ] ;; CS [ NeCTS' ] [owise] .

  op set : CTermSet -> Command{=>State} .
  ---------------------------------------
  eq set(CTS) [ CTS' ] = CTS .

  ops reduce rewrite narrow narrow-smt : -> Command{Module=>State} .
  ------------------------------------------------------------------
  ceq reduce     < MOD > [ T ] = T' if { T' , TYPE } := metaReduce(MOD, T) .
  eq  rewrite    < MOD > [ T ] = #rewrite(MOD, T, #varAway(MOD, T), 0) .
  eq  narrow     < MOD > [ T ] = #narrow(MOD, T, #varAway(MOD, T), 0) .
  eq  narrow-smt < MOD > [ T ] = #narrow-smt(MOD, T, #varAway(MOD, T), 0) .

  --- TODO: #varAway needs to actually make the generated variable away from `T`
  op #varAway : Module CTerm -> CTerm .
  -------------------------------------
  eq #varAway(MOD, T) = qid("X:" + string(getKind(MOD, leastSort(MOD, T)))) .

  op #rewrite : Module CTerm CTerm Nat -> CTermSet .
  --------------------------------------------------
  ceq #rewrite(MOD, T, T', N) = T'' ;; #rewrite(MOD, T, T', s(N)) if { T'' , TYPE , SUBST } := metaSearch(MOD, T, T', nil, '+, 1, N) .
  eq  #rewrite(MOD, T, T', N) = .CTermSet [owise] .

  --- TODO: If the term passed to `#narrow` is ground with no condition, is it a safe optimization to
  --- pass it to `#rewrite` instead?
  op #narrow : Module CTerm CTerm Nat -> CTermSet .
  -------------------------------------------------
  ceq #narrow(MOD, T, T', N) = T'' ;; #narrow(MOD, T, T', s(N)) if { T'' , TYPE , SUBST } := metaNarrow(MOD, T, T', '+, 1, N) .
  eq  #narrow(MOD, T, T', N) = .CTermSet [owise] .

  op #narrow-smt : Module CTerm CTerm Nat -> CTerm .
endfm
```

State Trace
-----------

We need to have a state trace around for trace-based analysis. This particular
trace tracks the accumulated seen states up to a step, as well as the states
first seen at that step.

```{.maude .meta-strategy}
fmod TRACE is
  protecting STATE .

  sorts CTermSetPair CTermSetPairMap CTermSetTrace .

  sorts Command{Module,State=>Trace} Command{=>Trace} .
  sort Command{Trace=>State} .

  var N : Nat . var MOD : Module . vars CTS CTS1 CTS2 : CTermSet . var CTSPM : CTermSetPairMap .

  op trace <_> : CTermSetTrace -> Analysis .
  ------------------------------------------

  op <_,_> : CTermSet CTermSet -> CTermSetPair .
  ----------------------------------------------

  op .CTermSetPairMap : -> CTermSetPairMap .
  op _|->_ : Nat CTermSetPair -> CTermSetPairMap [prec 64] .
  op __    : CTermSetPairMap CTermSetPairMap -> CTermSetPairMap [assoc comm id: .CTermSetPairMap prec 65 format(d n d)] .
  -----------------------------------------------------------------------------------------------------------------------

  op .CTermSetTrace : -> CTermSetTrace .
  op _|_            : Nat CTermSetPairMap -> CTermSetTrace [prec 66] .
  --------------------------------------------------------------------
  eq .CTermSetTrace = 0 | .CTermSetPairMap .

  op _<_,_> : Command{Module,State=>Trace} Module CTermSet -> Command{=>Trace} .
  op _<_>   : Command{Trace=>State} CTermSetTrace -> Command{=>State} .
  op _[_] : Command{=>Trace} CTermSetTrace -> [CTermSetTrace] .
  -------------------------------------------------------------

  op extend : -> Command{Module,State=>Trace} .
  ---------------------------------------------
  eq extend < MOD , CTS > [ 0    | .CTermSetPairMap            ] = s(0)    | 0 |-> < CTS , CTS > .
  eq extend < MOD , CTS > [ s(N) | CTSPM N |-> < CTS1 , CTS2 > ] = s(s(N)) | CTSPM N |-> < CTS1 , CTS2 > s(N) |-> < CTS -- CTS2 , CTS ++ CTS2 > .

  op load : -> Command{Trace=>State} .
  ------------------------------------
  eq load < s(N) | CTSPM N |-> < CTS1 , CTS2 > > [ CTS ] = CTS1 .
endfm
```

Strategy
--------

Finally, we need a strategy which will control all of this. Here I have a simple
imperative strategy language with boolean predicates over sets of terms.

```{.maude .meta-strategy}
fmod STRATEGY is
  protecting STATE .
  extending BOOL .
  protecting NAT .

  sorts BVar Command Program .
  subsort BVar < Bool .
  subsort Command < Program .

  sorts Command{State=>Strategy} Command{=>Strategy} .
  subsorts Command{State=>Strategy} Command{=>Strategy} < Command .

  vars P P' P1 P2 : Program . vars B B' : Bool . var N : Nat . var CTS : CTermSet . var NeCTS : NeCTermSet .

  op strategy <_> : Program -> Analysis .
  ---------------------------------------

  op .Program : -> Program .
  op _;_ : Program Program -> Program [assoc id: .Program prec 75] .
  ------------------------------------------------------------------

  op #bool : Bool -> Command .
  op ?_:_  : Program Program -> Program [strat(0)] .
  --------------------------------------------------
  eq #bool(true)  ; ? P1 : P2 = P1 .
  eq #bool(false) ; ? P1 : P2 = P2 .

  op {_} : Program -> Program .
  -----------------------------
  eq { P } = P .

  op if_then_else_ : Bool Program Program -> Program [prec 72 strat(0)] .
  -----------------------------------------------------------------------
  eq if B then P1 else P2 = state-predicate(B) ; ? P1 : P2 .

  op while__ : Bool Program -> Program [prec 72 strat(0)] .
  ---------------------------------------------------------
  eq while B P = if B then { P ; while B P } else .Program .

  op repeat__ : Nat Program -> Program [prec 72 strat(0)] .
  ---------------------------------------------------------
  eq repeat 0    P = .Program .
  eq repeat s(N) P = P ; repeat N P .

  op _<_> : Command{State=>Strategy} CTermSet -> Command{=>Strategy} .
  op _[_] : Command{=>Strategy} Program -> [Program] .
  ----------------------------------------------------

  op state-predicate : Bool -> Command{State=>Strategy} .
  -------------------------------------------------------
  eq state-predicate(B) < CTS > [ P ] = #bool(#eval(B, CTS)) ; P .

  op #eval : Bool CTermSet -> [Bool] .
  ------------------------------------
  eq #eval(true        , CTS) = true .
  eq #eval(false       , CTS) = false .
  eq #eval(  not     B', CTS) = not #eval(B', CTS) .
  eq #eval(B or      B', CTS) = #eval(B, CTS) or      #eval(B', CTS) .
  eq #eval(B and     B', CTS) = #eval(B, CTS) and     #eval(B', CTS) .
  eq #eval(B xor     B', CTS) = #eval(B, CTS) xor     #eval(B', CTS) .
  eq #eval(B implies B', CTS) = #eval(B, CTS) implies #eval(B', CTS) .

  op empty? : -> BVar .
  ---------------------
  eq #eval(empty?, .CTermSet) = true .
  eq #eval(empty?, NeCTS)     = false .
endfm
```

MSH
---

When the above state components are put together (in a parallel manner), then
what you get is `MSH`. `MSH` contains some of the functionality of the normal
Maude shell (eg. `reduce`, `rewrite`, and `narrow`), but defined in an
extensible and programmable way.

This module consists of the "plumbing" for `MSH`, which loads arguments from the
correct parts of the state and applies the results to the correct parts of the
state. This is all done using the sorts of the commands .

```{.maude .meta-strategy}
fmod MSH is
  protecting MODULE .
  protecting STATE .
  protecting TRACE .
  extending STRATEGY .

  var P : Program . var MOD : Module . var CTermS : CTermSet . var CTermST : CTermSetTrace .

  var CM : Command{=>Module} .
  var CMS : Command{Module=>State} . var CTS : Command{Trace=>State} . var CS : Command{=>State} .
  var CSSt : Command{State=>Strategy} . var CSt : Command{=>Strategy} .
  var CMST : Command{Module,State=>Trace} . var CT : Command{=>Trace} .

  subsort Command{=>Module} < Command .
  -------------------------------------
  eq strategy < CM ; P > current-module < MOD >
   = strategy <      P > current-module < CM [ MOD ] > .
  
  subsorts Command{Module=>State} Command{Trace=>State} Command{=>State} < Command .
  ----------------------------------------------------------------------------------
  eq strategy < CMS         ; P > current-module < MOD >
   = strategy < CMS < MOD > ; P > current-module < MOD > .

  eq strategy < CTS             ; P > trace < CTermST >
   = strategy < CTS < CTermST > ; P > trace < CTermST > .

  eq strategy < CS ; P > state < CTermS >
   = strategy < P      > state < CS [ CTermS ] > .

  --- subsorts Command{State=>Strategy} Command{=>Strategy} < Command .
  ---------------------------------------------------------------------
  eq strategy < CSSt            ; P > state < CTermS >
   = strategy < CSSt < CTermS > ; P > state < CTermS > .

  eq strategy < CSt ; P >
   = strategy < CSt [ P ] > .

  subsorts Command{Module,State=>Trace} Command{=>Trace} < Command .
  ------------------------------------------------------------------
  eq strategy < CMST                  ; P > current-module < MOD > state < CTermS >
   = strategy < CMST < MOD , CTermS > ; P > current-module < MOD > state < CTermS > .

  eq strategy < CT ; P > trace < CTermST >
   = strategy <      P > trace < CT [ CTermST ] > .
endfm
```

Narrowing modulo SMT
====================

Here we instantiate all the above given components to a language suitable for
narrowing modulo SMT trace-based analysis.

```{.maude .meta-strategy}
fmod NARROWING-MODULO-SMT is
  protecting MSH .

  op explore-all : -> Program .
  -----------------------------
  eq explore-all = extend
                 ; while (not empty?) { narrow
                                      ; extend
                                      ; load
                                      } .
endfm
```

Examples
========

Rewrite Cycle
-------------

This module just rewrites in a simple cycle.

```{.maude .example-cycle}
load meta-strategy

mod CYCLE is
  sorts PreState State .

  ops a b c : -> PreState .

  ops f g : PreState -> State .

  rl f(a) => f(b) .
  rl f(a) => g(c) .
  rl f(b) => f(c) .
  rl f(c) => f(a) .
endm


reduce in NARROWING-MODULO-SMT :

current-module < upModule('CYCLE, true) >
trace < .CTermSetTrace >
state < 'f['X:PreState] >
strategy < set-module('CYCLE) ; explore-all >

.

q
```

Nondeterministic Scheduler
--------------------------

This implements the worlds simplest and dumbest scheduler.

```{.maude .example-nondet-scheduler}
load meta-strategy

fmod SCHEDULER is
  sorts Task NeTasks Tasks .
  subsorts Task < NeTasks < Tasks .
  sort State .

  op .Tasks : -> Tasks .
  op __ : NeTasks Tasks -> NeTasks [assoc comm id: .Tasks] .
  op __ : Tasks   Tasks -> Tasks   [ditto] .

  vars NeTS : NeTasks .
  eq NeTS NeTS = NeTS .

  op {_} : Tasks -> State .
  op _|_ : Task Tasks -> State .

  ops ta tb tc : -> Task .
  op addTasks    : Tasks -> Task .
  op removeTasks : Tasks -> Task .

  vars TS TS' : Tasks . var T : Task .
  eq addTasks(TS)      | TS'   = {TS TS'} .
  eq removeTasks(T TS) | T TS' = removeTasks(T TS) | TS' .
  eq removeTasks(TS)   | TS'   = {TS'} [owise] .
endfm

mod NONDET-SCHEDULER is
  protecting SCHEDULER .

  var T : Task . var TS : Tasks .
  rl { T TS } => T | TS .
  rl T | TS   => { TS } .
endm

reduce in NARROWING-MODULO-SMT :

current-module < upModule('NONDET-SCHEDULER, true) >
trace < .CTermSetTrace >
state < '`{_`}['__['tb.Task, 'addTasks['__['ta.Task, 'tb.Task]]]] >
strategy < set-module('NONDET-SCHEDULER) ; explore-all >

.

q
```
