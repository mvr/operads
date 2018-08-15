-- Copyright 2009 Mikael Vejdemo Johansson <mik@stanford.edu>
-- Released under a BSD license

-- | Implements decorated and ordered trees, and most operations acting only on these.
-- The decorated tree is the most fundamental part of the implementation, and the internal
-- structure of the tree is to the largest extent what determines the actual identity
-- of a given element of the free operad.

module Math.Operad.OrderedTree where

import Prelude hiding (mapM)
import Data.Foldable (Foldable, foldMap)
import Data.Traversable
import Data.List (sort, sortBy, intersperse, nub, findIndices)
import Data.Ord
import Control.Monad.State hiding (mapM)

import Math.Operad.PPrint

-- * Decorated and ordered trees

-- | The fundamental tree data type used. Leaves carry labels - most often integral -
-- and these are expected to control, e.g., composition points in shuffle operad compositions.
-- The vertices carry labels, used for the ordering on trees and to distinguish different
-- basis corollas of the same arity.
data PreDecoratedTree a b
  = DTLeaf !b |
    DTVertex {
      vertexType :: !a,
      subTrees :: ![PreDecoratedTree a b]
    }
  deriving (Eq, Ord, Read, Show)

-- | The arity of a corolla
vertexArity :: PreDecoratedTree a b -> Int
vertexArity t = length (subTrees t)

instance Functor (PreDecoratedTree a) where
    fmap f (DTLeaf b) = DTLeaf (f b)
    fmap f (DTVertex t ts) = DTVertex t (map (fmap f) ts)

instance Foldable (PreDecoratedTree a) where
    foldMap f (DTLeaf b) = f b
    foldMap f (DTVertex _ ts) = mconcat (map (foldMap f) ts)

instance Traversable (PreDecoratedTree a) where
    traverse f (DTLeaf b) = DTLeaf <$> f b
    traverse f (DTVertex t ts) = DTVertex t <$> traverse (traverse f) ts

instance (Show a, Show b) => PPrint (PreDecoratedTree a b) where
    pp (DTLeaf x) = show x
    pp (DTVertex t ts) = "m" ++ show t ++ "(" ++ concat (intersperse "," (map pp ts)) ++ ")"

-- | Apply a function @f@ to all the internal vertex labels of a PreDecoratedTree.
vertexMap :: (a -> b) -> PreDecoratedTree a c -> PreDecoratedTree b c
vertexMap _ (DTLeaf i) = DTLeaf i
vertexMap f (DTVertex t ts) = DTVertex (f t) (map (vertexMap f) ts)

-- | If a tree has trees as labels for its leaves, we can replace the leaves with the roots of
-- those label trees. Thus we may glue together trees, as required by the compositions.
glueTrees :: PreDecoratedTree a (PreDecoratedTree a b) -> PreDecoratedTree a b
glueTrees (DTLeaf newRoot) = newRoot
glueTrees (DTVertex t ts) = DTVertex t (map glueTrees ts)

instance Applicative (PreDecoratedTree a) where
  pure = return
  (<*>) = ap

instance Monad (PreDecoratedTree a) where
  return = DTLeaf
  a >>= f = glueTrees (fmap f a)

-- | This is the fundamental datatype of the whole project. Monomials in a free operad
-- are decorated trees, and we build a type for decorated trees here. We require our
-- trees to have Int labels, limiting us to at most 2 147 483 647 leaf labels.
type DecoratedTree a = PreDecoratedTree a Int

-- | Monomial orderings on the free operad requires us to choose an ordering for the
-- trees. These are parametrized by types implementing the type class 'TreeOrdering',
-- and this is a data type for a tree carrying its comparison type. We call these
-- /ordered trees/.
data OrderedTree a t = OT (DecoratedTree a) t deriving (Eq, Show, Read)

instance (Show a, TreeOrdering t) => PPrint (OrderedTree a t) where
    pp (OT dect _) = pp dect

-- | Monomial ordering for trees. We require this to be a total well-ordering, compatible
-- with the operadic compositions.
instance (Ord a, TreeOrdering t) => Ord (OrderedTree a t) where
    compare (OT s o1) (OT t _) = treeCompare o1 s t

-- | Building an ordered tree with 'PathLex' ordering from a decorated tree.
ot :: (Ord a, TreeOrdering t) => DecoratedTree a -> OrderedTree a t
ot t = OT t ordering

-- | Extracting the underlying tree from an ordered tree.
dt :: (Ord a, TreeOrdering t) => OrderedTree a t -> DecoratedTree a
dt (OT t _) = t




-- ** Monomial orderings on the free operad

-- | The type class that parametrizes types implementing tree orderings.
class (Eq t, Show t) => TreeOrdering t where
    treeCompare :: Ord a => t -> DecoratedTree a -> DecoratedTree a -> Ordering
    treeCompare o t1 t2 = comparePathSequence o t1 (orderedPathSequence t1) t2 (orderedPathSequence t2)
    comparePathSequence :: Ord a => t -> DecoratedTree a -> ([[a]],Shuffle) -> DecoratedTree a -> ([[a]],Shuffle) -> Ordering
    ordering :: t

-- | Finding the path sequences. cf. Dotsenko-Khoroshkin.
pathSequence :: DecoratedTree a -> ([[a]],Shuffle)
pathSequence (DTLeaf j) = ([[]],[j])
pathSequence (DTVertex l ts) = let
    pathSequences = map pathSequence $! ts
    paths = concatMap fst $! pathSequences
    leaves = concatMap snd $! pathSequences
  in (map (l:) $! paths, leaves)

-- | Reordering the path sequences to mirror the actual leaf ordering.
orderedPathSequence :: DecoratedTree a -> ([[a]], Shuffle)
orderedPathSequence t = (map fst . sortBy (comparing snd) $ zip ps1 ps2, ps2)
  where (ps1, ps2) = pathSequence t

-- | Changes direction of an ordering.
reverseOrder :: Ordering -> Ordering
reverseOrder LT = GT
reverseOrder GT = LT
reverseOrder EQ = EQ


-- | Using the path sequence, the leaf orders and order reversal, we can get 8 different orderings
-- from one paradigm. These are given by 'PathPerm', 'RPathPerm', 'PathRPerm', 'RPathRPerm' for the
-- variations giving (possibly reversed) path sequence comparison precedence over (possibly reversed)
-- leaf permutations; additionally, there are 'PermPath', 'RPermPath', 'PermRPath' and 'RPermRPath'
-- for the variations with the opposite precedence.

data PathPerm = PathPerm deriving (Eq, Ord, Show, Read)
instance TreeOrdering PathPerm where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cs = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else comp1) clS coS
                         in
                           if any (/= EQ) cs then head (filter (/=EQ) cs)
                           else compare perms permt
    ordering = PathPerm

data RPathPerm = RPathPerm deriving (Eq, Ord, Show, Read)
instance TreeOrdering RPathPerm where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cS = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else reverseOrder comp1) clS coS
                         in
                           if any (/= EQ) cS then head (filter (/=EQ) cS)
                           else compare perms permt
    ordering = RPathPerm

data PathRPerm = PathRPerm deriving (Eq, Ord, Show, Read)
instance TreeOrdering PathRPerm where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cs = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else comp1) clS coS
                         in
                           if any (/= EQ) cs then head (filter (/=EQ) cs)
                           else reverseOrder $ compare perms permt
    ordering = PathRPerm

data RPathRPerm = RPathRPerm deriving (Eq, Ord, Show, Read)
instance TreeOrdering RPathRPerm where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cS = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else reverseOrder comp1) clS coS
                         in
                           if any (/= EQ) cS then head (filter (/=EQ) cS)
                           else reverseOrder $ compare perms permt
    ordering = RPathRPerm


data PermPath = PermPath deriving (Eq, Ord, Show, Read)
instance TreeOrdering PermPath where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cs = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else comp1) clS coS
                            test1 = compare perms permt
                         in
                           if test1 /= EQ then test1
                           else if any (/= EQ) cs then head (filter (/=EQ) cs) else EQ
    ordering = PermPath

data PermRPath = PermRPath deriving (Eq, Ord, Show, Read)

instance TreeOrdering PermRPath where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cS = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else reverseOrder comp1) clS coS
                            test1 = compare perms permt
                         in
                           if test1 /= EQ then test1
                           else if any (/= EQ) cS then head (filter (/=EQ) cS) else EQ
    ordering = PermRPath

data RPermPath = RPermPath deriving (Eq, Ord, Show, Read)
instance TreeOrdering RPermPath where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cs = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else comp1) clS coS
                            test1 = reverseOrder $ compare perms permt
                         in
                           if test1 /= EQ then test1
                           else if any (/= EQ) cs then head (filter (/=EQ) cs) else EQ
    ordering = RPermPath

data RPermRPath = RPermRPath deriving (Eq, Ord, Show, Read)
instance TreeOrdering RPermRPath where
    treeCompare o s t = if (nLeaves s) /= (nLeaves t) then comparing nLeaves s t
                        else if s == t then EQ
                        else comparePathSequence o s (orderedPathSequence s) t (orderedPathSequence t)
    comparePathSequence _ _ (paths,perms) _ (patht,permt) = let
                            clS = zipWith (comparing length) paths patht
                            coS = zipWith compare paths patht
                            cS = zipWith (\comp1 comp2 -> if comp1 == EQ then comp2 else reverseOrder comp1) clS coS
                            test1 = reverseOrder $ compare perms permt
                         in
                           if test1 /= EQ then test1
                           else if any (/= EQ) cS then head (filter (/=EQ) cS) else EQ
    ordering = RPermRPath


-- ** Utility functions on trees
--
-- Trees are represented rooted, and all operations act on a specific root, and may recurse from there.

-- | Build a single corolla in a decorated tree. Takes a list for labels for the leaves, and derives
-- the arity of the corolla from those. This, and the composition functions, form the preferred method
-- to construct trees.
corolla :: (Ord a, Show a) => a -> [Int] -> DecoratedTree a
corolla label leaflabels =
    if null leaflabels
    then error "The operadic Buchberger, and many other algorithms, require the absence of 0-ary operations."
    else DTVertex label (map DTLeaf leaflabels)

-- | Build a single leaf.
leaf :: Int -> DecoratedTree a
leaf n = DTLeaf n

-- | Check whether a given root is a leaf.
isLeaf :: DecoratedTree a -> Bool
isLeaf (DTLeaf _) = True
isLeaf _ = False

-- | Check whether a given root is a corolla.
isCorolla :: (Ord a, Show a) => DecoratedTree a -> Bool
isCorolla = not . isLeaf

-- | Change the leaves of a tree to take their values from a given list.
relabelLeaves :: (Ord a, Show a) => DecoratedTree a -> [b] -> PreDecoratedTree a b
relabelLeaves tree newLabels = fst $ runState (mapM (\_ -> do; (x:xs) <- get; put xs; return x) tree) newLabels

-- | Find the permutation the leaf labeling ordains for inputs.
leafOrder :: (Ord a, Show a) => DecoratedTree a -> [Int]
leafOrder = foldMap (:[])


-- | Find the minimal leaf covering any given vertex.
minimalLeaf :: Ord b => PreDecoratedTree a b -> b
minimalLeaf (DTLeaf lbl) = lbl
minimalLeaf vertex = minimum $ map minimalLeaf (subTrees vertex)

-- | Compute the number of leaves of the entire tree covering a given vertex.
nLeaves :: DecoratedTree a -> Int
nLeaves (DTLeaf _) = 1
nLeaves vertex = sum $ map nLeaves (subTrees vertex)

-- | 'arityDegree' is one less than 'nLeaves'.
arityDegree :: (Ord a, Show a) => DecoratedTree a -> Int
arityDegree t = nLeaves t - 1

-- * Shuffles
-- Basic handling functions for building, recognizing and applying shuffle permutations.

-- | A shuffle is a special kind of sequence of integers.
type Shuffle = [Int]

-- | We need to recognize sorted sequences of integers.
isSorted :: Ord a => [a] -> Bool
isSorted xs = and $ zipWith (<=) xs (tail xs)

-- | This tests whether a given sequence of integers really is a shuffle.
isShuffle :: Shuffle -> Bool
isShuffle as = (sort as) == [1..length as] &&
               any (\k -> isShuffleIJ as k (length as-k)) [1..length as]

-- | This tests whether a given sequence of integers is an (i,j)-shuffle
isShuffleIJ :: Shuffle -> Int -> Int -> Bool
isShuffleIJ as i j = isSorted [a | a <- as, a <= i] &&
                     isSorted [a | a <- as, a > i] &&
                     length as == i+j

-- | This tests whether a given sequence of integers is admissible for a specific composition operation.
isShuffleIPQ :: Shuffle -> Int -> Int -> Bool
isShuffleIPQ as i p = let
    initSegment = take i as
    finalSegment = drop i as
    upperTree = take p finalSegment
    latterTree = drop p finalSegment
  in initSegment == [1 .. length initSegment] &&
     isSorted upperTree &&
     isSorted latterTree

-- | This applies the resulting permutation from a shuffle to a set of elements
applyPerm :: Shuffle -> [a] -> [a]
applyPerm s is = --trace ("applyPerm " ++ show s ++ " " ++ show (length is) ++ "\n") $
                 map (is!!) (map (subtract 1) s)

-- | Apply the permutation inversely to 'applyPerm'.
invApplyPerm :: Shuffle -> [a] -> [a]
invApplyPerm sh lst = map snd . sortBy (comparing fst) $ zip sh lst

-- | Generate all subsets of length k from a given list.
kSubsets :: Int -> [Int] -> [[Int]]
kSubsets 0 _ = [[]]
kSubsets k ss = if length ss == k then [ss]
                else if length ss < k then []
                else do
                  map sort $ (map ((head ss):) $ kSubsets (k-1) (tail ss)) ++ kSubsets k (tail ss)

-- | Applies @f@ only at the @n@th place in a list.
applyAt :: (a -> a) -> Int -> [a] -> [a]
applyAt f n as = take n as ++ [f (as !! n)] ++ drop (n+1) as

-- | Picks out the last nonzero entry in a list.
lastNonzero :: (Eq a, Num a) => [a] -> Int
lastNonzero as = let
    ras = reverse as
    dwz = dropWhile (==0) ras
    lnzi = length dwz - 1
  in lnzi

-- | Generates shuffle permutations by filling buckets.
allShPerm :: Int -> [Int] -> [[[Int]]]
allShPerm 0 as = [replicate (length as) []]
allShPerm n as = do
  let
      lastIndex = filter (>=0) [lastNonzero as]
      indices = nub $ (findIndices (>1) as) ++ lastIndex
  i <- indices
  p <- allShPerm (n-1) (applyAt (subtract 1) i as)
  return (applyAt (++[n]) i p)

-- | Generates all shuffles from Sh_i(p,q).
allShuffles :: Int -> Int -> Int -> [Shuffle]
allShuffles i p q = map concat $ allShPerm (i+p+q) ((replicate (i-1) 1) ++ [p+1] ++ (replicate q 1))
