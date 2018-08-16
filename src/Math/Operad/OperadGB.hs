{-# language CPP #-}
-- Copyright 2009 Mikael Vejdemo Johansson <mik@stanford.edu>
-- Released under a BSD license

-- | The module 'OperadGB' carries the implementations of the Buchberger algorithm and most utility functions
-- related to this.

module Math.Operad.OperadGB where

import Prelude hiding (mapM, sequence)
import Data.Bifunctor
import Data.Coerce
import Data.List (sort, sortBy, findIndex, nub, (\\))
import Data.Ord
import Control.Monad hiding (mapM)
import Data.Maybe

import Math.Operad.MapOperad

import Math.Operad.OrderedTree

#ifdef TRACE
import Debug.Trace
import Math.Operad.PPrint
#endif

-- * Fundamental data types and instances

-- | The number of internal vertices of a tree.
operationDegree :: DecoratedTree a -> Int
operationDegree (DTLeaf _) = 0
operationDegree vertex = 1 + sum (map operationDegree (subTrees vertex))

-- | A list of operation degrees occurring in the terms of the operad element
operationDegrees :: OperadElement a n t -> [Int]
operationDegrees op = foldMonomials (\(k,_) lst -> lst ++ [(operationDegree . dt $ k)]) op

-- | The maximal operation degree of an operadic element
maxOperationDegree :: OperadElement a n t -> Int
maxOperationDegree element = if null op then 0 else maximum op
  where op = operationDegrees element

-- | Check that an element of a free operad is homogenous
isHomogenous :: OperadElement a n t -> Bool
isHomogenous m = let
    trees = getTrees m
--    equalityCheck :: OrderedTree a t -> OrderedTree a t -> Bool
    equalityCheck s t = arityDegree (dt s) == arityDegree (dt t) &&
                        operationDegree (dt s) == operationDegree (dt t)
  in and $ zipWith (equalityCheck) trees (tail trees)

-- * Free operad

-- ** Operadic compositions

-- | Composition in the shuffle operad
shuffleCompose :: Int -> Shuffle -> DecoratedTree a -> DecoratedTree a -> DecoratedTree a
shuffleCompose i sh s t | not (isPermutation sh) = error "shuffleCompose: sh needs to be a permutation\n"
                        | (nLeaves s) + (nLeaves t) - 1 /= length sh =
                            error $ "Permutation permutes the wrong number of things:" -- ++ show i ++ " " ++ show sh ++ " " ++ show s ++ " " ++ show t ++ "\n"
                        | not (isShuffleIPQ sh i (nLeaves t-1)) =
                            error $ "Need a correct pointed shuffle permutation!\n" -- ++
                                  -- show sh ++ " is not in Sh" ++ show i ++
                                  --          "(" ++ show (nLeaves t-1) ++ "," ++ show (nLeaves s-i) ++ ")\n"
                        | otherwise = symmetricCompose i sh s t

-- | Composition in the non-symmetric operad. We compose s o_i t.
nsCompose :: Int -> DecoratedTree a -> DecoratedTree a -> DecoratedTree a
nsCompose i s t = if i-1 > nLeaves s then error "Composition point too large"
                  else let
                      pS = rePackLabels s
                      lookupList = zip (leafOrder s) (leafOrder pS)
                      idx = if isNothing newI then error "Index not in tree" else fromJust newI where newI = lookup i lookupList
                      trees = map DTLeaf [1..nLeaves s]
                      newTrees = take (idx-1) trees ++ [t] ++ drop idx trees
                 in
                   if length newTrees /= nLeaves s then error "Shouldn't happen"
                   else
                     nsComposeAll s newTrees

-- | Composition in the symmetric operad
symmetricCompose :: Int -> Shuffle -> DecoratedTree a -> DecoratedTree a -> DecoratedTree a
symmetricCompose i sh s t = if not (isPermutation sh) then error "symmetricCompose: sh needs to be a permutation\n"
                            else if (nLeaves s) + (nLeaves t) - 1 /= length sh then error "Permutation permutes the wrong number of things.\n"
                            else fmap ((sh!!) . (subtract 1)) $  nsCompose i s t

-- | Non-symmetric composition in the g(s;t1,...,tk) style.
nsComposeAll :: DecoratedTree a -> [DecoratedTree a] -> DecoratedTree a
nsComposeAll s trees = if nLeaves s /= length trees then error "NS: Need as many trees as leaves\n"
                        else if length trees == 0 then s
                        else let
                            treesArities = map nLeaves trees
                            packedTrees = map rePackLabels trees
                            offSets = (0:) $ scanl1 (+) treesArities
                            newTrees = zipWith (\t n -> fmap (+n) t) packedTrees offSets
                          in
                            rePackLabels $ glueTrees $ fmap ((newTrees!!) . (subtract 1)) $ rePackLabels s

-- | Verification for a shuffle used for the g(s;t1,..,tk) style composition in the shuffle operad.
checkShuffleAll :: Shuffle -> [Int] -> Bool
checkShuffleAll sh blockL = let
      checkOrders :: Shuffle -> [Int] -> Bool
      checkOrders [] _ = True
      checkOrders _ [] = True
      checkOrders restSh restBlock = (isSorted (take (head restBlock) restSh)) &&
                                     (length restSh <= head restBlock ||
                                      (head restSh) < (head (drop (head restBlock) restSh))) &&
                                     checkOrders (drop (head restBlock) restSh) (tail restBlock)
    in
      sum blockL == length sh &&
      checkOrders sh blockL

-- | Sanity check for permutations.
isPermutation :: Shuffle -> Bool
isPermutation sh = and ((zipWith (==) [1..]) (sort sh))

-- | Shuffle composition in the g(s;t1,...,tk) style.
shuffleComposeAll :: Shuffle -> DecoratedTree a -> [DecoratedTree a] -> DecoratedTree a
shuffleComposeAll sh s trees = if nLeaves s /= length trees then error "Shuffle: Need as many trees as leaves\n"
                               else if sum (map nLeaves trees) /= length sh then error "Permutation permutes the wrong number of things.\n"
                               else if not (isPermutation sh) then error "shuffleComposeAll: sh needs to be a permutation\n"
                               else if length trees == 0 then s
                                    else if not (checkShuffleAll sh (map nLeaves trees)) then error "Bad shuffle"
                                         else let
      newTree = nsComposeAll s trees
   in
            fmap ((sh!!) . (subtract 1)) newTree

-- | Symmetric composition in the g(s;t1,...,tk) style.
symmetricComposeAll :: Shuffle -> DecoratedTree a -> [DecoratedTree a] -> DecoratedTree a
symmetricComposeAll sh s trees = if nLeaves s /= length trees then error "Symm: Need as many trees as leaves\n"
                               else if sum (map nLeaves trees) /= length sh then error "Permutation permutes the wrong number of things.\n"
                               else if not (isPermutation sh) then error "sh needs to be a permutation"
                               else if length trees == 0 then s
                                         else let
      newTree = nsComposeAll s trees
   in
            fmap ((sh!!) . (subtract 1)) newTree




-- ** Divisibility among trees

-- | Data type to move the results of finding an embedding point for a subtree in a larger tree
-- around. The tree is guaranteed to have exactly one corolla tagged Nothing, the subtrees on top of
-- that corolla sorted by minimal covering leaf in the original setting, and the shuffle carried around
-- is guaranteed to restore the original leaf labels before the search.
type Embedding a = DecoratedTree (Maybe a)

-- | Returns True if there is a subtree of @t@ isomorphic to @s@, respecting leaf orders.
divides :: Eq a => DecoratedTree a -> DecoratedTree a -> Bool
divides s t = not . null $ findAllEmbeddings s t

-- | Returns True if there is a subtree of @t@ isomorphic to @s@, respecting leaf orders, and not located at the root.
dividesHigh :: Eq a => DecoratedTree a -> DecoratedTree a -> Bool
dividesHigh s t = not . null $ concatMap (findAllEmbeddings s) (subTrees t)

-- | Returns True if there is a rooted subtree of @t@ isomorphic to @s@, respecting leaf orders.
dividesRooted :: Eq a => DecoratedTree a -> DecoratedTree a -> Bool
dividesRooted s t = isJust $ findRootedEmbedding s t

-- | Finds all ways to embed s into t respecting leaf orders.
findAllEmbeddings :: Eq a => DecoratedTree a -> DecoratedTree a -> [Embedding a]
findAllEmbeddings _ (DTLeaf _) = []
findAllEmbeddings s t = let
    rootFind = maybeToList $ findRootedEmbedding s t
    subFinds = map (findAllEmbeddings s) (subTrees t)
    reGlue (i, ems) = let
        glueTree tree =
            (DTVertex
             (Just $ vertexType t)
             (take (i-1) (map toJustTree $ subTrees t) ++ [tree] ++ drop i (map toJustTree $ subTrees t)))
      in map glueTree ems
  in rootFind ++ concatMap reGlue (zip [1..] subFinds)

-- | Helper function for 'findRootedEmbedding'.
findUnsortedRootedEmbedding :: (Eq a) => DecoratedTree a -> DecoratedTree a -> Maybe (Embedding a)
findUnsortedRootedEmbedding (DTLeaf _) t = Just (DTVertex Nothing [toJustTree t])
findUnsortedRootedEmbedding (DTVertex _ _) (DTLeaf _) = Nothing
findUnsortedRootedEmbedding s t = do
  guard $ vertexArity s == vertexArity t
  guard $ vertexType s == vertexType t
  let mTreeFinds = zipWith findUnsortedRootedEmbedding (subTrees s) (subTrees t)
  guard $ all isJust mTreeFinds
  let treeFinds = map fromJust mTreeFinds
  guard $ all (isNothing . vertexType) treeFinds
  guard $ equivalentOrders (leafOrder s) (concatMap (map minimalLeaf . subTrees) treeFinds)
  return $ DTVertex Nothing (concatMap subTrees treeFinds)

-- | Finds all ways to embed s into t, respecting leaf orders and mapping the root of s to the root of t.
findRootedEmbedding :: Eq a => DecoratedTree a -> DecoratedTree a -> Maybe (Embedding a)
findRootedEmbedding s t = do
  re <- findUnsortedRootedEmbedding s t
  return $ DTVertex Nothing (sortBy (comparing minimalLeaf) (subTrees re))

-- | Checks a tree for planarity.
planarTree :: DecoratedTree a -> Bool
planarTree (DTLeaf _) = True
planarTree (DTVertex _ subs) = all planarTree subs && isSorted (map minimalLeaf subs)

-- | Returns True if s and t divide u, with different embeddings and t sharing root with u.
dividesDifferent :: (Eq a) => DecoratedTree a -> DecoratedTree a -> DecoratedTree a -> Bool
dividesDifferent s t u = dividesRooted t u &&
                         if s /= t
                         then
                             divides s u
                         else
                             dividesHigh s u



-- | Interchanges @Left@ to @Right@ and @Right@ to @Left@ for types @Either a a@
flipEither :: Either a a -> Either a a
flipEither (Left a) = Right a
flipEither (Right a) = Left a

-- | Projects the type @Either a a@ onto the type @a@ in the obvious manner.
stripEither :: Either a a -> a
stripEither (Left a) = a
stripEither (Right a) = a

-- | Applies @flipEither@ to the root vertex label of a tree.
flipEitherRoot :: PreDecoratedTree (Either a a) b -> PreDecoratedTree (Either a a) b
flipEitherRoot l@(DTLeaf _) = l
flipEitherRoot (DTVertex t ts) = DTVertex (flipEither t) ts

-- | Projects vertex labels and applies leaf labels to a tree with internal labeling in @Either a a@.
fuseTree :: DecoratedTree (Either a a) -> [Int] -> DecoratedTree (Either a a)
fuseTree t ls = flip relabelLeaves ls $ t

-- | Strips the @Either@ layer from internal vertex labels
stripTree :: DecoratedTree (Either a a) -> DecoratedTree a
stripTree = first stripEither

-- | Acquires lists for resorting leaf labels according to the algorithm found for
-- constructing small common multiples with minimal work.
leafOrders :: DecoratedTree a -> DecoratedTree b -> [(Int,Int)]
leafOrders (DTLeaf si) u = [(si,minimalLeaf u)]
leafOrders s (DTLeaf ui) = [(minimalLeaf s, ui)]
leafOrders s u = concat $ zipWith leafOrders (subTrees s) (subTrees u)

-- | Locates the first vertex tagged with a @Right@ constructor in a tree labeled with @Either a b@.
findFirstRight :: DecoratedTree (Either a b) -> Maybe (DecoratedTree (Either a b))
findFirstRight (DTLeaf _) = Nothing
findFirstRight (DTVertex (Left _) ts) =  listToMaybe $ mapMaybe findFirstRight ts
findFirstRight v@(DTVertex (Right _) _) = Just v

-- | Equivalent to listToMaybe . reverse
maybeLast :: [a] -> Maybe a
maybeLast [] = Nothing
maybeLast as = Just $ last as

-- | Recursive algorithm to figure out correct leaf labels for a reconstructed small common multiple of two trees.
leafLabels :: DecoratedTree a -> [Int] -> [Int] -> [[Int]]
leafLabels u tl1 tl2 = let
    leafLabelsAcc :: Int -> [([Int], [Int], [Int])] -> [[Int]]
    leafLabelsAcc 0 accs = map (\(_,_,a) -> a) accs
    leafLabelsAcc n accs = let
        newaccs = do
          (tau1,tau2,out) <- accs
          let
              t1 = maybeLast tau1
              t2 = maybeLast tau2
              tt1 = if isNothing t1 || (fromJust t1) `elem` take (length tau2 - 1) tau2 then [] else maybeToList t1
              tt2 = if isNothing t2 || (fromJust t2) `elem` take (length tau1 - 1) tau1 then [] else maybeToList t2
              tt = nub $ tt1 ++ tt2
          t <- tt
          return $ (tau1 \\ [t], tau2 \\ [t], applyAt (const n) t out)
      in leafLabelsAcc (n-1) newaccs
  in leafLabelsAcc (nLeaves u) [(tl1, tl2, (replicate (nLeaves u) 0))]

-- | Finds rooted small common multiples of two trees.
findRootedSCM :: (Eq a) =>
                 DecoratedTree a -> DecoratedTree a -> Maybe (DecoratedTree a)
findRootedSCM s (DTLeaf _) = Just s
findRootedSCM (DTLeaf _) t = Just t
findRootedSCM s t = do
  guard $ vertexType s == vertexType t
  let stSCMs = zipWith findRootedSCM (subTrees s) (subTrees t)
  guard $ all isJust stSCMs
  let stSCM = map fromJust stSCMs
  return $ relabelLeaves (DTVertex (vertexType s) (stSCM)) [1..]

-- | Finds structural small common multiples, disregarding leaf labels completely.
findNonSymmetricSCM :: (Eq a) =>
                       Int -> DecoratedTree (Either a a) -> DecoratedTree (Either a a) -> [DecoratedTree (Either a a)]
findNonSymmetricSCM _ _ (DTLeaf _) = []
findNonSymmetricSCM _ (DTLeaf _) _ = []
findNonSymmetricSCM 0 _ _ = []
findNonSymmetricSCM n s t = let
      rootedSCMs = if (operationDegree s) > n || (operationDegree t) > n then []
                   else maybeToList $ fmap flipEitherRoot $ findRootedSCM s t
      childSCMs = map (findNonSymmetricSCM (n-1) s) (subTrees t)
      zippedChildSCMs = zip [0..] childSCMs
      zippedChildren = do
        (i, cSCMs) <- zippedChildSCMs
        child <- cSCMs
        return $ DTVertex (vertexType t) (applyAt (const child) i (subTrees t))
  in nub $ map (flip relabelLeaves [1..]) $ rootedSCMs ++ zippedChildren

-- | Finds small common multiples of two trees bounding internal operation degree.
findBoundedSCM :: (Eq a) => Int -> DecoratedTree a -> DecoratedTree a -> [DecoratedTree (Either a a)]
findBoundedSCM n s t = do
  em <- findNonSymmetricSCM n (first Left s) (first Left t)
  guard $ isJust $ findFirstRight em
  let lot = leafOrders t em
      los = leafOrders s (fromJust $ findFirstRight em)
      tau1 = map (subtract 1) $ map snd $ sort lot
      tau2 = map (subtract 1) $ map snd $ sort los
  leaves <- nub $ leafLabels em tau1 tau2
  let retTree = fuseTree em leaves
  guard $ operationDegree retTree <= n
  return retTree

-- | Finds all small common multiples of two trees.
findAllSCM :: (Eq a) => DecoratedTree a -> DecoratedTree a -> [DecoratedTree (Either a a)]
findAllSCM s t = nub $ (findBoundedSCM maxBound s t)

-- | Finds all small common multiples of two trees, bounding the internal operation degree.
findAllBoundedSCM :: (Eq a) => Int -> DecoratedTree a -> DecoratedTree a -> [DecoratedTree (Either a a)]
findAllBoundedSCM n s t = nub $ (findBoundedSCM n s t)

-- | Constructs embeddings for @s@ and @t@ in @SCM(s,t)@ and returns these.
scmToEmbedding :: (Eq a) => DecoratedTree (Either a a) -> DecoratedTree a -> DecoratedTree a -> (Embedding a, Embedding a)
scmToEmbedding scm s t = let
    lEm = findRootedEmbedding t (stripTree scm)
  --findHighEmbedding :: DecoratedTree (Either a a) -> Maybe (Embedding a)
    findHighEmbedding (DTLeaf _) = Nothing
    findHighEmbedding (DTVertex (Left tp) ts) = Just $
                                               DTVertex
                                               (Just tp)
                                               (zipWith (\ss tt -> if isJust ss then fromJust ss else tt)
                                                            (map findHighEmbedding ts)
                                                            (map (first Just) $ map stripTree ts))
    findHighEmbedding v@(DTVertex (Right _) _) = findRootedEmbedding s (stripTree v)
    rEm = findHighEmbedding scm
  in if isNothing lEm || isNothing rEm
     then error ("Bad SCM in scmToEmbedding"
#ifdef TRACE
                 ++ ": lEm is " ++ pp lEm ++ " and rEm is " ++ pp rEm ++ " for\n\t" ++ show s ++ "\n\t" ++ show t ++ "\n\t" ++ show scm
#endif
                )
     else (fromJust lEm, fromJust rEm)

-- | Relabels a tree in the right order, but with entries from [1..]
rePackLabels :: Ord b => PreDecoratedTree a b -> DecoratedTree a
rePackLabels tree = fmap (fromJust . (flip lookup (zip (sort (foldMap (:[]) tree)) [1..]))) tree

-- | Removes vertex type encapsulations.
fromJustTree :: DecoratedTree (Maybe a) -> Maybe (DecoratedTree a)
fromJustTree (DTLeaf k) = Just (DTLeaf k)
fromJustTree (DTVertex Nothing _) = Nothing
fromJustTree (DTVertex (Just l) sts) = let
    newsts = map fromJustTree sts
  in
    if all isJust newsts then Just $ DTVertex l (map fromJust newsts)
    else Nothing

-- | Adds vertex type encapsulations.
toJustTree :: DecoratedTree a -> DecoratedTree (Maybe a)
toJustTree (DTLeaf k) = DTLeaf k
toJustTree (DTVertex a sts) = DTVertex (Just a) (map toJustTree sts)

-- replace the following function by one that zips lists, sorts them once, and then unsplits them,
-- verifying both lists to be sorted afterwards?

-- | Verifies that two integer sequences correspond to the same total ordering of the entries.
equivalentOrders :: [Int] -> [Int] -> Bool
equivalentOrders o1 o2 = if length o1 /= length o2 then False
                         else let
                             c1 = map snd . sort . zip o1 $ [(1::Int)..]
                             c2 = map snd . sort . zip o2 $ [(1::Int)..]
                           in
                             c1 == c2

-- | Returns True if any of the vertices in the given tree has been tagged.
subTreeHasNothing :: DecoratedTree (Maybe a) -> Bool
subTreeHasNothing (DTLeaf _) = False
subTreeHasNothing (DTVertex Nothing _) = True
subTreeHasNothing (DTVertex (Just _) sts) = any subTreeHasNothing sts

-- | The function that mimics resubstitution of a new tree into the hole left by finding embedding,
-- called m_\alpha,\beta in Dotsenko-Khoroshkin. This version only attempts to resubstitute the tree
-- at the root, bailing out if not possible.
reconstructNode :: DecoratedTree a -> Embedding a -> Maybe (DecoratedTree a)
reconstructNode sub super = if isJust (vertexType super) then Nothing
                            else if (nLeaves sub) /= (vertexArity super) then Nothing
                            else let
                                newSubTrees = map fromJustTree (subTrees super)
                           in
                             if any isNothing newSubTrees then Nothing
                             else let
                                 base = rePackLabels sub
                                 newTrees = map fromJust newSubTrees
                               in
                                 Just $ glueTrees $ fmap ((newTrees !!) . (subtract 1)) base

-- | The function that mimics resubstitution of a new tree into the hole left by finding embedding,
-- called m_\alpha,\beta in Dotsenko-Khoroshkin. This version recurses down in the tree in order
-- to find exactly one hole, and substitute the tree sub into it.
reconstructTree :: DecoratedTree a -> Embedding a -> Maybe (DecoratedTree a)
reconstructTree sub super = if isLeaf super then Nothing
                            else if isNothing (vertexType super) then reconstructNode sub super
                            else if (1/=) . sum . map fromEnum $ map subTreeHasNothing (subTrees super) then Nothing
                            else
                                      let
                                          fromMaybeBy f s t = if isNothing t then f s else t
                                          subtreesSuper = subTrees super
                                          reconstructions = map (reconstructTree sub) subtreesSuper
                                          results = zipWith (fromMaybeBy fromJustTree) subtreesSuper reconstructions
                                      in
                                        if any isNothing results then Nothing
                                           else Just $ DTVertex (fromJust $ vertexType super) (map fromJust results)


-- ** Groebner basis methods

-- | Applies the reconstruction map represented by em to all trees in the operad element op. Any operad element that
-- fails the reconstruction (by having the wrong total arity, for instance) will be silently dropped. We recommend
-- you apply this function only to homogenous operad elements, but will not make that check.
applyReconstruction :: (Ord a, TreeOrdering t, Eq n, Num n) => Embedding a -> OperadElement a n t -> OperadElement a n t
applyReconstruction em m = let
      reconstructor (ordT, n) = do
        newDT <- reconstructTree (dt ordT) em
        return $ (ot newDT, n)
    in oe $ mapMaybe reconstructor (toList m)

-- | Finds all S polynomials for a given list of operad elements.
findAllSPolynomials :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                       [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
findAllSPolynomials = findInitialSPolynomials maxBound

-- | Finds all S polynomials for which the operationdegree stays bounded.
findInitialSPolynomials :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                           Int -> [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
findInitialSPolynomials n oldGb newGb = nub . map (\o -> (1/leadingCoefficient o) .*. o) . filter (not . isZero) $ do
    g1 <- oldGb ++ newGb
    g2 <- newGb
    findSPolynomials n g1 g2 ++ findSPolynomials n g2 g1

-- | Finds all S polynomials for a given pair of operad elements, keeping a bound on operation degree.
findSPolynomials :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                           Int -> OperadElement a n t -> OperadElement a n t -> [OperadElement a n t]
findSPolynomials n g1 g2 = do
    let
        lmg1 = leadingMonomial g1
        lmg2 = leadingMonomial g2
        cf12 = (leadingCoefficient g1) / (leadingCoefficient g2)
    scm <- findAllBoundedSCM n lmg1 lmg2
    let (mg2, mg1) = scmToEmbedding scm lmg1 lmg2
    return $ (applyReconstruction mg1 g1) - (cf12 .*. (applyReconstruction mg2 g2))

-- | Non-symmetric version of 'findInitialSPolynomials'.
findNSInitialSPolynomials :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                           Int -> [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
findNSInitialSPolynomials n oldGB newGB = nub . map (\o -> (1/leadingCoefficient o) .*. o) . filter (not . isZero) $ do
    g1 <- oldGB ++ newGB
    g2 <- newGB
    findNSSPolynomials n g1 g2 ++ findNSSPolynomials n g2 g1

-- | Non-symmetric version of 'findSPolynomials'.
findNSSPolynomials :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                           Int -> OperadElement a n t -> OperadElement a n t -> [OperadElement a n t]
findNSSPolynomials n g1 g2 = do
  let
      lmg1 = leadingMonomial g1
      lmg2 = leadingMonomial g2
      cf12 = (leadingCoefficient g1) / (leadingCoefficient g2)
  scm <- findNonSymmetricSCM n (first Left lmg1) (first Left lmg2)
  let (mg2,mg1) = scmToEmbedding scm lmg1 lmg2
  return $ (applyReconstruction mg1 g1) - (cf12 .*. (applyReconstruction mg2 g2))

-- | Reduce g with respect to f and the embedding em: lt f -> lt g.
reduceOE :: (Ord a, TreeOrdering t, Eq n, Fractional n) => Embedding a -> OperadElement a n t -> OperadElement a n t -> OperadElement a n t
reduceOE em f g = if not (divides (leadingMonomial f) (leadingMonomial g))
                  then g
                  else let
                      cgf = (leadingCoefficient g) / (leadingCoefficient f)
                      ret = g - (cgf .*. (applyReconstruction em f))
                    in
                      ret

-- | Reduce the leading monomial of @op@ with respect to @gb@.
reduceInitial :: (Ord a, TreeOrdering t, Eq n, Fractional n) => OperadElement a n t -> [OperadElement a n t] -> OperadElement a n t
reduceInitial op [] = op
reduceInitial op gb = if isZero op
                         then op
                         else let
                             divisorIdx = findIndex (flip divides (leadingMonomial op)) (map leadingMonomial gb)
                           in
                             if isNothing divisorIdx then op
                             else
                               let
                                 g1 = gb!!(fromJust divisorIdx)
                                 em = head $ findAllEmbeddings (leadingMonomial g1) (leadingMonomial op)
                                 o1 = reduceOE em g1 op
                                in
                                 reduceInitial o1 gb

-- | Reduce all terms of @op@ with respect to @gbn@.
reduceCompletely :: (Ord a, TreeOrdering t, Eq n, Fractional n) => OperadElement a n t -> [OperadElement a n t] -> OperadElement a n t
reduceCompletely op [] = op
reduceCompletely op gbn =
    if isZero op then op
    else let
        gb = filter (not . isZero) gbn
        nop = reduceInitial op gb
      in
        if nop == op then leadingOTerm op + (reduceCompletely (op - (leadingOTerm op)) gb)
        else reduceCompletely nop gb

-- | Perform one iteration of the Buchberger algorithm: generate all S-polynomials. Reduce all S-polynomials.
-- Return anything that survived the reduction.
stepOperadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                          [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
stepOperadicBuchberger oldGb newGb = stepInitialOperadicBuchberger maxBound oldGb newGb

stepNSOperadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                          [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
stepNSOperadicBuchberger oldGB newGB = stepNSInitialOperadicBuchberger maxBound oldGB newGB

-- | Perform one iteration of the Buchberger algorithm: generate all S-polynomials. Reduce all S-polynomials.
-- Return anything that survived the reduction. Keep the occurring operation degrees bounded.
stepInitialOperadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                          Int -> [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
stepInitialOperadicBuchberger maxD oldGb newGb =
    nub $
    filter (not . isZero) $
    do
  spol <- findInitialSPolynomials maxD oldGb newGb
  guard $ maxOperationDegree spol <= maxD
  let red =
          reduceCompletely spol (oldGb ++ newGb)
  guard $ not . isZero $ red
  return red

-- | Non-symmetric version of 'stepInitialOperadicBuchberger'.
stepNSInitialOperadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                          Int -> [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
stepNSInitialOperadicBuchberger maxD oldGb newGb =
    nub $
    filter (not . isZero) $
    do
  spol <- findNSInitialSPolynomials maxD oldGb newGb
  guard $ maxOperationDegree spol <= maxD
  let red =
          reduceCompletely spol (oldGb ++ newGb)
  guard $ not . isZero $ red
  return red

-- | Perform the entire Buchberger algorithm for a given list of generators. Iteratively run the single iteration
-- from 'stepOperadicBuchberger' until no new elements are generated.
--
-- DO NOTE: This is entirely possible to get stuck in an infinite loop. It is not difficult to write down generators
-- such that the resulting Groebner basis is infinite. No checking is performed to catch this kind of condition.
operadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) => [OperadElement a n t] -> [OperadElement a n t]
operadicBuchberger gb = nub $ streamOperadicBuchberger maxBound (reduceBasis [] gb)

-- | Non-symmetric version of 'operadicBuchberger'.
nsOperadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) => [OperadElement a n t] -> [OperadElement a n t]
nsOperadicBuchberger gb = nub $ streamNSOperadicBuchberger maxBound (reduceBasis [] gb)

-- | Perform the entire Buchberger algorithm for a given list of generators. This iteratively runs single iterations
-- from 'stepOperadicBuchberger' until no new elements are generated.
streamOperadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                            Int -> [OperadElement a n t] -> [OperadElement a n t]
streamOperadicBuchberger maxOD gb = let
    stepOnce _ [] [] = []
    stepOnce stable unstable new = let
        newgb = stepInitialOperadicBuchberger maxOD (stable++unstable) new
        minArity = minimum (maxBound : (map (nLeaves . leadingMonomial) newgb))
        unstables = unstable ++ new
        newStable = reduceBasis stable $ reverse $ filter ((<minArity) . nLeaves . leadingMonomial) unstables
        stableCandidates = stable ++ reduceBasis stable (reverse newStable)
        unstableCandidates = reverse $ unstables \\ stableCandidates
        midUnstable = reduceBasis stableCandidates unstableCandidates
        newUnstable = reduceBasis stableCandidates (reverse midUnstable)
      in newStable ++ stepOnce stableCandidates newUnstable newgb
  in stepOnce [] [] gb

-- | Non-symmetric version of 'streamOperadicBuchberger'.
streamNSOperadicBuchberger :: (Ord a, TreeOrdering t, Eq n, Fractional n) =>
                            Int -> [OperadElement a n t] -> [OperadElement a n t]
streamNSOperadicBuchberger maxOD gb = let
    stepOnce _ [] [] = []
    stepOnce stable unstable new = let
        newgb = stepNSInitialOperadicBuchberger maxOD (stable++unstable) new
        minArity = minimum (maxBound : (map (nLeaves . leadingMonomial) newgb))
        unstables = unstable ++ new
        newStable = reduceBasis stable $ filter ((<minArity) . nLeaves . leadingMonomial) unstables
        unstableCandidates = unstables \\ newStable
        newUnstable = reduceBasis newStable unstableCandidates
        newNew = reduceBasis [] newgb
      in newStable ++ stepOnce newStable newUnstable newNew
  in stepOnce [] [] gb

-- | Reduces a list of elements with respect to all other elements occurring in that same list.
reduceBasis :: (Eq n, Fractional n, TreeOrdering t, Ord a) =>
               [OperadElement a n t] -> [OperadElement a n t] -> [OperadElement a n t]
reduceBasis ogb ngb = let
    reduceStep _ [] = []
    reduceStep gb (g:gs) = let
                           ng = reduceCompletely g gb
                           output = if isZero ng then [] else [ng]
                      in
                        output ++ reduceStep (gb ++ output) gs
  in
    reduceStep ogb (reverse $ reduceStep ogb (reverse ngb))

-- ** Low degree bases

-- | All trees composed from the given generators of operation degree n.
allTrees :: (Ord a) =>
            [DecoratedTree a] -> Int -> [DecoratedTree a]
allTrees _ 0 = []
allTrees gens 1 = gens
allTrees gens k = nub $ do
  gen <- gens
  tree <- allTrees gens (k-1)
  let degC = nLeaves gen
      degT = nLeaves tree
  i <- [1..degT]
  shuffle <- allShuffles i (degC - 1) (degT - i)
  return $ shuffleCompose i shuffle tree gen

-- | Generate basis trees for a given Groebner basis for degree 'maxDegree'. 'divisors' is expected
-- to contain the leading monomials in the Groebner basis.
basisElements :: (Ord a) =>
                 [DecoratedTree a] -> [DecoratedTree a] -> Int -> [DecoratedTree a]
basisElements generators divisors maxDegree = nub $
    if maxDegree <= 0 then []
    else if maxDegree == 1 then generators
         else do
           b <- basisElements generators divisors (maxDegree-1)
           gen <- generators
           let degC = nLeaves gen
               degT = nLeaves b
           i <- [1..degT]
           shuffle <- allShuffles i (degC-1) (degT-i)
           let newB = shuffleCompose i shuffle b gen
           guard $ not $ any (flip divides newB) divisors
           return newB

-- | Change the monomial order used for a specific tree. Use this in conjunction with mapMonomials
-- in order to change monomial order for an entire operad element.
changeOrder :: OrderedTree a s -> OrderedTree a t
changeOrder = coerce
