```haskell
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
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

class Functor n => Reduce n d where
    reduce :: Term n d -> Term n d

    reduceAll :: Term n d -> Term n d
    reduceAll (Node n) = reduce $ Node (fmap reduceAll n)
    reduceAll d        = reduce d
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
    fmap f (Z)   = Z
    fmap f (S a) = S (f a)

type SNatInt = Term SNat IntData

z :: SNatInt
z = Node Z
--- alternatively z = int 0

s :: SNatInt -> SNatInt
s n = Node (S n)

pn :: Integer -> SNatInt
pn 0         = z
pn n | n > 0 = s $ pn (n - 1)

p :: SNatInt -> SNatInt -> SNatInt
p (Node (S x)) y = Node (S (p x y))
p (Node Z)     y = y

t :: SNatInt -> SNatInt -> SNatInt
t (Node (S x)) y = p (t x y) y
t (Node Z)     y = z

instance Reduce SNat IntData where
    reduce (Node Z)       = z
    reduce (Node (S a))   = s a
    reduce (Node (P a b)) = p a b
    reduce (Node (T a b)) = t a b
```

A free Ring over `IntData`
--------------------------

```haskell
data Ring a = Neg   a
            | Plus  a a
            | Times a a
            | Zero
            | One
            deriving (Show, Eq)

instance Functor Ring where
    fmap f (Plus  a b) = Plus  (f a) (f b)
    fmap f (Neg a)     = Neg (f a)
    fmap f (Times a b) = Times (f a) (f b)
    fmap f (Zero)      = Zero
    fmap f (One)       = One
```

Here are some "smart constructors" for the `Ring` data-structure, that make it
nicer to build a `Ring` and potentially perform some simplification of the
resulting `Ring`.

Here, I've built some simplification into the operators. Multiplication is
distributed, and variables are gathers to the right (integer to the left).
Negatives propagate inward.

```haskell
type RingInt = Term Ring IntData

zero :: RingInt
zero = int 0

one :: RingInt
one = int 1

neg :: RingInt -> RingInt
neg (Data (I i))       = Data (I (- i))
neg (Data (V i))       = Node $ Neg (Data (V i))
neg (Node (Plus a b))  = Node $ Plus (neg a) (neg b)
neg (Node (Times a b)) = Node $ Times (neg a) b
neg a                  = Node $ Neg a

plus :: RingInt -> RingInt -> RingInt
plus (Node Zero)         b                 = b
plus a                   (Node Zero)       = plus zero a
plus (Node One)          (Data (I i))      = int (i + 1)
plus a                   (Node One)        = plus one a
plus (Data (I i1))       (Data (I i2))     = int (i1 + i2)
plus a@(Data (V _))      (Node (Plus b c)) = plus b (plus a c)
plus a                   (Node (Plus b c)) = plus (plus a b) c
--- plus p@(Node (Plus _ _)) b                 = plus b p
plus a                   b                 = Node $ Plus a b

times :: RingInt -> RingInt -> RingInt
times (Node Zero)          b                  = zero
times a                    (Node Zero)        = times zero a
times (Node One)           b                  = b
times a                    (Node One)         = a
times (Data (I i1))        (Data (I i2))      = int (i1 * i2)
times a@(Data (V _))       (Node (Times b c)) = times b (times a c)
times a                    (Node (Times b c)) = times (times a b) c
times t@(Node (Times _ _)) b                  = times b t
times a                    (Node (Plus b c))  = plus (times a b) (times a c)
times a                    (Node (Neg b))     = times (neg a) b
times a                    b                  = Node $ Times a b

instance Reduce Ring IntData where
    reduce (Node Zero)        = zero
    reduce (Node One)         = one
    reduce (Node (Neg a))     = neg a
    reduce (Node (Plus a b))  = plus a b
    reduce (Node (Times a b)) = times a b
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

Sets
----

```haskell
data Set a = Set a
           | MtSet
           | Union a a
           deriving (Show, Eq)

instance Functor Set where
    fmap f (Set a)     = Set (f a)
    fmap f (MtSet)     = MtSet
    fmap f (Union a b) = Union (f a) (f b)

type SetInt = Term Set IntData

mt :: SetInt
mt = Node MtSet

set :: Int -> SetInt
set n = Node (Set (Data (I n)))

union :: SetInt -> SetInt -> SetInt
union (Node MtSet) b                      = b                   --- MtSet is left-id
union a (Node MtSet)                      = a                   --- MtSet is right-id
union a b | a == b                        = a                   --- idempotence
union (Node (Union a b)) c                = union a (union b c) --- idempotence
union a (Node (Union b c)) = let ab = union a b
                             in  if ab == b then Node $ Union b c else union ab c
--- union a@(Node (Set _)) (Node (Union b c)) = union b (union a c) --- idempotence
union a@(Node (Set _)) b@(Node (Set _))   = Node (Union a b)    --- base case
```
