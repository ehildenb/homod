{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}


--- Algebraic Structure
--- ===================

--- We would like to represent $T_{\Sigma}$, a term algebra. We can also represent
--- $T_{\Sigma}(X)$, the free $T_{\Sigma}$ algebra over data (set) $X$.

--- Terms will either be pieces of data, (from $X$, what the algebra is free over),
--- or operators (from $\Sigma$).


data Term n d = Data d
              | Node (n (Term n d))

instance (Show d, Show (n (Term n d))) => Show (Term n d) where
    show (Data d) = show d
    show (Node n) = "(" ++ show n ++ ")"

instance (Eq d, Eq (n (Term n d))) => Eq (Term n d) where
    Data d == Data d' = d == d'
    Node n == Node n' = n == n'
    _      == _       = False


--- Data
--- ----

--- Apply an operation to the data a term is constructed over.


onData :: Functor n => (d -> Term n d) -> Term n d -> Term n d
onData f (Data d) = f d
onData f (Node n) = Node (fmap (onData f) n)


--- Leaf data is what our term algebra will be free over. Here, we say integers and
--- variables.


data IntData = V String
             | I Int
             deriving Eq

instance Show IntData where
    show (V s) = "var(" ++ s ++ ")"
    show (I i) = show i


--- Here we have a particular substitution.

--- Example Algebras
--- ================

--- We have to make the algebras instance of `Functor`. This makes sure that we can
--- traverse over the resulting `Term`.

--- A free Ring on the underlying data
--- ----------------------------------


data Ring a = Plus  a a
            | Minus a a
            | Times a a
            | Zero
            | One
            deriving (Show, Eq)

instance Functor Ring where
    fmap f (Plus  a b) = Plus  (f a) (f b)
    fmap f (Minus a b) = Minus (f a) (f b)
    fmap f (Times a b) = Times (f a) (f b)
    fmap f (Zero)      = Zero
    fmap f (One)       = One


--- Here are some "smart constructors" for the `Ring` data-structure, that make it
--- nicer to build a `Ring` and potentially perform some simplification of the
--- resulting `Ring`.


type RingInt = Term Ring IntData

zero :: RingInt
zero = Node Zero

one :: RingInt
one = Node One

plus :: RingInt -> RingInt -> RingInt
plus a b = Node (Plus a b)

minus :: RingInt -> RingInt -> RingInt
minus a b = Node (Minus a b)

times :: RingInt -> RingInt -> RingInt
times a b = Node (Times a b)

rvar :: String -> RingInt
rvar = Data . V

rint :: Int -> RingInt
rint = Data . I


--- The `if_then_else_` construct
--- -----------------------------


data ITE a = ITE Bool a a

instance Functor ITE where
    fmap f (ITE b a a') = ITE b (f a) (f a')

--- ite :: Bool -> RingInt -> RingInt -> RingInt
--- ite b i1 i2 = Node (ITE b i1 i2)


--- The Peano naturals
--- ------------------


data Peano a = Z
             | S a
             deriving (Show, Eq)

instance Functor Peano where
    fmap f (Z)   = Z
    fmap f (S a) = S (f a)

type PeanoNat = Term Peano IntData

z :: PeanoNat
z = Node Z

s :: PeanoNat -> PeanoNat
s n = Node (S n)

pn :: Integer -> PeanoNat
pn 0         = z
pn n | n > 0 = s $ pn (n - 1)

pplus :: PeanoNat -> PeanoNat -> PeanoNat
pplus (Node (S x)) y = Node (S (pplus x y))
pplus (Node Z)     y = y

ptimes :: PeanoNat -> PeanoNat -> PeanoNat
ptimes (Node (S x)) y = pplus (ptimes x y) y
ptimes (Node Z)     y = z


--- Sets
--- ----


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

