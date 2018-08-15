{-# language CPP #-}
-- Copyright 2009 Mikael Vejdemo Johansson <mik@stanford.edu>
-- Released under a BSD license

-- | Implements the operad element storage using the Haskell native Data.Map storage type.

module Math.Operad.MapOperad where

#ifndef USE_OLDMAP
import qualified Math.Operad.Map as Map
import Math.Operad.Map (Map)
#else
import qualified Data.Map as Map
import Data.Map (Map)
#endif
import Data.Maybe
import Math.Operad.OrderedTree
import Math.Operad.PPrint

#ifndef USE_OLDMAP
type MonomialMap a t n = Map a t n
#else
type MonomialMap a t n = Map (OrderedTree a t) n
#endif

-- | The type carrying operadic elements. An element in an operad is an associative array
-- with keys being labeled trees and values being their coefficients.
newtype OperadElement a n t = OE (MonomialMap a t n) deriving (Eq, Ord, Show, Read)

instance (Ord a, Show a, Show n, TreeOrdering t) => PPrint (OperadElement a n t) where
      pp (OE m) = if str == "" then "0" else str
          where str = Map.foldWithKey (\k a result -> result ++ "\n+" ++ show a ++ "*" ++ pp k) "" m

-- | Extracting the internal structure of the an element of the free operad.
extractMap :: (Ord a, Show a, TreeOrdering t) => OperadElement a n t -> MonomialMap a t n
extractMap (OE m) = m

-- | Arithmetic in the operad.
instance (Ord a, Show a, Eq n, Num n, TreeOrdering t) => Num (OperadElement a n t) where
    (OE m) + (OE n) = OE $ Map.filter (/=0) $ Map.unionWith (+) m n
    negate on = (-1).*.on
    (OE m) * (OE n) = OE $ Map.filter (/=0) $ Map.intersectionWith (*) m n
    abs _ = undefined
    signum _ = undefined
    fromInteger _ = undefined

-- | Scalar multiplication in the operad.
(.*.) :: (Ord a, Num n, TreeOrdering t) => n -> OperadElement a n t -> OperadElement a n t
nn .*. (OE m) = OE $ Map.map (nn*) m

-- | Apply a function to each monomial tree in the operad element.
mapMonomials :: (Ord b, Num n, TreeOrdering t) =>
                (OrderedTree a s -> OrderedTree b t) -> OperadElement a n s -> OperadElement b n t
mapMonomials f (OE m) = OE $ Map.mapKeysWith (+) f m

-- | Fold a function over all monomial trees in an operad element, collating the results in a list.
foldMonomials :: (Ord a, TreeOrdering t) =>
                 ((OrderedTree a t,n) -> [b] -> [b]) -> OperadElement a n t -> [b]
foldMonomials f (OE m) = Map.foldWithKey (curry f) [] m

-- | Given a list of (tree,coefficient)-pairs, reconstruct the corresponding operad element.
fromList :: (TreeOrdering t, Show a, Ord a, Eq n, Num n) => [(OrderedTree a t,n)] -> OperadElement a n t
fromList = OE . Map.filter (/=0) . Map.fromListWith (+)

-- | Given an operad element, extract a list of (tree, coefficient) pairs.
toList :: (TreeOrdering t, Show a, Ord a) => OperadElement a n t -> [(OrderedTree a t, n)]
toList (OE m) = Map.toList m

-- ** Handling polynomials in the free operad

-- | Construct an element in the free operad from its internal structure. Use this instead of the constructor.
oe :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => [(OrderedTree a t, n)] -> OperadElement a n t
oe = fromList

-- | Construct a monomial in the free operad from a tree and a tree ordering. It's coefficient will be 1.
oet :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => DecoratedTree a -> OperadElement a n t
oet dect = oe $ [(OT dect ordering, 1)]

-- | Construct a monomial in the free operad from a tree, a tree ordering and a coefficient.
oek :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => DecoratedTree a -> n -> OperadElement a n t
oek dect n = oe $ [(OT dect ordering, n)]

-- | Return the zero of the corresponding operad, with type appropriate to the given element.
-- Can be given an appropriately casted undefined to construct a zero.
zero :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => OperadElement a n t
zero = oe [(ot $ leaf 1, 0)]

-- | Check whether an element is equal to 0.
isZero :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => OperadElement a n t -> Bool
isZero (OE m) = Map.null $ Map.filter (/=0) m

-- | Extract the leading term of an operad element as an operad element.
leadingOTerm :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => OperadElement a n t -> OperadElement a n t
leadingOTerm om = oe [leadingTerm om]

-- | Extract the leading term of an operad element.
leadingTerm :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => OperadElement a n t -> (OrderedTree a t, n)
leadingTerm (OE om) = fromMaybe (ot (leaf 0), 0) $ do
                        ((m,c),_) <- Map.maxViewWithKey om
                        return (m,c)

-- | Extract the ordered tree for the leading term of an operad element.
leadingOMonomial :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => OperadElement a n t -> OrderedTree a t
leadingOMonomial = fst . leadingTerm

-- | Extract the tree for the leading term of an operad element.
leadingMonomial :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => OperadElement a n t -> DecoratedTree a
leadingMonomial = dt .leadingOMonomial

-- | Extract the leading coefficient of an operad element.
leadingCoefficient :: (Ord a, Show a, TreeOrdering t, Eq n, Num n) => OperadElement a n t -> n
leadingCoefficient = snd . leadingTerm

-- | Extract all occurring monomial trees from an operad element.
getTrees :: (TreeOrdering t, Show a, Ord a) => OperadElement a n t -> [OrderedTree a t]
getTrees (OE m) = Map.keys m
