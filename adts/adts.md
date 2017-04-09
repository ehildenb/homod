```haskell
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
```

Algebraic Structure
===================

We would like to represent $T_{\Sigma}$, a term algebra. We can also represent
$T_{\Sigma}(X)$, the free $T_{\Sigma}$ algebra over data (set) $X$.

Terms will either be pieces of data, (from $X$, what the algebra is free over),
or operators (from $\Sigma$).

```haskell
data Term n d = Data d
              | Node (n (Term n d))

instance (Show d, Show (n (Term n d))) => Show (Term n d) where
    show (Data d) = show d
    show (Node n) = "(" ++ show n ++ ")"

instance (Eq d, Eq (n (Term n d))) => Eq (Term n d) where
    Data d == Data d' = d == d'
    Node n == Node n' = n == n'
    _      == _       = False

class Reifiable n d where
    reify :: (Reducable n) => d -> Term n d
    --- unreify :: (Reducable n) => Term n d -> Term n d

class (Functor n) => Reducable n where
    reduce :: n (Term n d) -> Term n d

    reduceAll :: Term n d -> Term n d
    reduceAll (Node n) = reduce $ fmap reduceAll n
    reduceAll (Data d) = Data d

    --- Law (idempotence):
    --- reduce . reduce == reduce

class Modelable n d where
    model :: Term n d -> Term n d
```

Data
----

Apply an operation to the data a term is constructed over.

```haskell
onData :: Functor n => (d -> Term n d) -> Term n d -> Term n d
onData f (Data d) = f d
onData f (Node n) = Node (fmap (onData f) n)
```

Leaf data is what our term algebra will be free over. Here, we say integers and
variables.

```haskell
data IntData = V String
             | I Int
             deriving Eq

instance Show IntData where
    show (V s) = show s
    show (I i) = show i

int :: Int -> Term n IntData
int = Data . I

var :: String -> Term n IntData
var = Data . V
```

Here we have a particular substitution.

```haskell
subst :: IntData -> Term a IntData
subst (V "x") = Data (I 3)
subst (V "y") = Data (I 2)
subst intData = Data intData
```

Example Algebras
================

We have to make the algebras instance of `Functor`. This makes sure that we can
traverse over the resulting `Term`.

Naturals
--------

```haskell
data SNat a = Z
            | S a
            | P a a
            | T a a
            deriving (Show, Eq)

instance Functor SNat where
    fmap f (Z)     = Z
    fmap f (S a)   = S (f a)
    fmap f (P a b) = P (f a) (f b)
    fmap f (T a b) = T (f a) (f b)

--- instance Reducable SNat where

type SNatInt = Term SNat

z :: SNatInt d
z = Node Z

s :: SNatInt d -> SNatInt d
s n = Node (S n)

p :: SNatInt d -> SNatInt d -> SNatInt d
p a b = Node (P a b)

t :: SNatInt d -> SNatInt d -> SNatInt d
t a b = Node (T a b)

snat :: Integer -> SNatInt d
snat 0         = z
snat n | n > 0 = s $ snat (n - 1)

--- vars a b .
---
--- eq P Z     b = b .
--- eq P (S a) b = S (P a b) .
---
--- eq T Z     b = Z .
--- eq T (S a) b = P b (T a b) .

instance Reducable SNat where
    reduce (P (Node Z) b)     = b
    reduce (P (Node (S a)) b) = Node (S (reduce $ P a b))
    reduce (T (Node Z) b)     = Node Z
    reduce (T (Node (S a)) b) = reduce $ P (reduce $ T a b) b
    reduce n                  = Node n

instance Reifiable SNat IntData where
    reify (I 0)         = Node Z
    reify (I n) | n > 0 = Node (S (reify (I $ n - 1)))
    reify (V v)         = var v

instance Modelable SNat IntData where
    model (Node Z)     = int 0
    model (Node (S a)) = case model a of
                             Data (I i) -> int (i + 1)
                             Data (V v) -> var v
```

A free Ring over `IntData`
--------------------------

```haskell
data Ring a = Zero
            | One
            | Neg a
            | Plus a a
            | Times a a
            deriving (Show, Eq)

instance Functor Ring where
    fmap f (Zero)      = Zero
    fmap f (One)       = One
    fmap f (Neg a)     = Neg (f a)
    fmap f (Plus  a b) = Plus (f a) (f b)
    fmap f (Times a b) = Times (f a) (f b)
```

Here are some "smart constructors" for the `Ring` data-structure, that make it
nicer to build a `Ring` and potentially perform some simplification of the
resulting `Ring`.

Here, I've built some simplification into the operators. Multiplication is
distributed, and variables are gathers to the right (integer to the left).
Negatives propagate inward.

```haskell
type RingInt = Term Ring

zero :: RingInt d
zero = Node Zero

one :: RingInt d
one = Node One

neg :: RingInt d -> RingInt d
neg = Node . Neg

plus :: RingInt d -> RingInt d -> RingInt d
plus a b = Node $ Plus a b

times :: RingInt d -> RingInt d -> RingInt d
times a b = Node $ Times a b

ring :: Int -> RingInt d
ring 0         = zero
ring n | n > 0 = plus (ring (n - 1)) one

--- vars a b .
---
--- eq Neg (Neg a)    = a .
--- eq Neg (Plus a b) = Plus (Neg a) (Neg b) .
---
--- eq Plus a Zero = a .
--- eq Plus Zero b = b .
---
--- eq Times (Neg a) b    = Neg (Times a b) .
--- eq Times a (Neg b)    = Neg (Times a b) .
--- eq Times a (Plus b c) = Plus (Times a b) (Times a c) .
--- eq Times (Plus a b) c = Plus (Times a c) (Times b c) .
--- eq Times a One        = a .
--- eq Times One b        = b .
--- eq Times a Zero       = Zero .
--- eq Times Zero b       = Zero .

add1 :: RingInt d -> RingInt d
add1 (reduceAll -> Node (Neg a)) = Node $ Plus (Node (Neg a)) (Node One)

instance Reducable Ring where
    reduce (Neg (Node (Neg a)))    = a
    reduce (Neg (Node (Plus a b))) = let na = reduce $ Neg a
                                         nb = reduce $ Neg b
                                     in  reduce $ Plus na nb

    reduce (Plus a (Node Zero)) = a
    reduce (Plus (Node Zero) b) = b

    reduce (Times (Node (Neg a)) b)    = reduce $ Neg (reduce $ Times a b)
    reduce (Times a (Node (Neg b)))    = reduce $ Neg (reduce $ Times a b)
    reduce (Times a (Node (Plus b c))) = let ab = reduce $ Times a b
                                             ac = reduce $ Times a c
                                         in  reduce $ Plus ab ac
    reduce (Times (Node (Plus a b)) c) = let ac = reduce $ Times a c
                                             bc = reduce $ Times b c
                                         in  reduce $ Plus ac bc
    reduce (Times a (Node One))  = a
    reduce (Times (Node One) b)  = b
    reduce (Times a (Node Zero)) = Node Zero
    reduce (Times (Node Zero) b) = Node Zero

    reduce n = Node n
```

The `if_then_else_` construct
-----------------------------

```haskell
data ITE a = ITE Bool a a

instance Functor ITE where
    fmap f (ITE b a a') = ITE b (f a) (f a')

--- ite :: Bool -> RingInt -> RingInt -> RingInt
--- ite b i1 i2 = Node (ITE b i1 i2)
```

Lists
-----

```
data List a = Nil
            | a : List a
            | List a ++ List a

eq (a : b) ++ c = a : (b ++ c) .
eq Nil     ++ c = c .
```

Sets
----

```haskell
data Set a = Set a
           | MtSet
           | a :+ a
           deriving (Show, Eq)

instance Functor Set where
    fmap f (Set a)  = Set (f a)
    fmap f (MtSet)  = MtSet
    fmap f (a :+ b) = (f a) :+ (f b)

type SetInt = Term Set IntData

mt :: SetInt
mt = Node MtSet

set :: Int -> SetInt
set n = Node (Set (Data (I n)))
--- 
--- union :: SetInt -> SetInt -> SetInt
--- union (Node MtSet) b                      = b                   --- MtSet is left-id
--- union a (Node MtSet)                      = a                   --- MtSet is right-id
--- union a b | a == b                        = a                   --- idempotence
--- union (Node (Union a b)) c                = union a (union b c) --- idempotence
--- union a (Node (Union b c)) = let ab = union a b
---                              in  if ab == b then Node $ Union b c else union ab c
--- --- union a@(Node (Set _)) (Node (Union b c)) = union b (union a c) --- idempotence
--- union a@(Node (Set _)) b@(Node (Set _))   = Node (Union a b)    --- base case
```
