-- Copyright 2009 Mikael Vejdemo Johansson <mik@stanford.edu>
-- Released under a BSD license

-- | The module 'Math.Operad.Map' is a thin wrapper around 'Data.Map', built to maintain the
-- particular needs of the Operads package.

module Math.Operad.Map where

import Prelude hiding (map)
import qualified Prelude as P
import qualified Data.Map as M
import Math.Operad.OrderedTree
import Control.Arrow

data StoredTree a t = ST [[a]] [Int] (OrderedTree a t) deriving (Show, Read, Eq)

sot :: OrderedTree a t -> StoredTree a t
sot pdt = let
    (path,perm) = orderedPathSequence (dt pdt)
  in ST path perm pdt

dot :: StoredTree a t -> OrderedTree a t
dot (ST _ _ pdt) = pdt

instance (Ord a, TreeOrdering t) => Ord (StoredTree a t) where
    compare (ST pathseq pathperm (OT t o)) (ST pathseq' pathperm' (OT s _)) =
        comparePathSequence o t (pathseq,pathperm) s (pathseq', pathperm')

data Map a t v = TM (M.Map (StoredTree a t) v) deriving (Show, Read, Eq, Ord)

filter :: (v -> Bool) -> Map a t v -> Map a t v
filter f (TM m) = TM $ M.filter f m

foldWithKey :: (OrderedTree a t -> v -> b -> b) -> b -> Map a t v -> b
foldWithKey f i (TM m) = M.foldrWithKey (\k val acc -> f (dot k) val acc) i m

fromListWith :: (Ord a, TreeOrdering t) =>
                (v -> v -> v) -> [(OrderedTree a t, v)] -> Map a t v
fromListWith f lst = TM $ M.fromListWith f (P.map (first sot) lst)

intersectionWith :: (Ord a, TreeOrdering t) =>
                    (u -> v -> w) -> Map a t u -> Map a t v -> Map a t w
intersectionWith f (TM m) (TM n) = TM $ M.intersectionWith f m n

keys :: Map a t v -> [OrderedTree a t]
keys (TM m) = P.map dot . M.keys $ m

map :: (v -> w) -> Map a t v -> Map a t w
map f (TM m) = TM $ M.map f m

mapKeysWith :: (Ord b, TreeOrdering s) =>
               (v -> v -> v) -> (OrderedTree a t -> OrderedTree b s) -> Map a t v -> Map b s v
mapKeysWith c f (TM m) = TM $ M.mapKeysWith c (sot . f . dot) m

maxViewWithKey :: Map a t v -> Maybe ((OrderedTree a t, v), Map a t v)
maxViewWithKey (TM m) = fmap (\((t,v),mmap) -> ((dot t, v), TM mmap)) . M.maxViewWithKey $ m

null :: Map a t v -> Bool
null (TM m) = M.null m

toList :: Map a t v -> [(OrderedTree a t, v)]
toList (TM m) = P.map (first dot) (M.toList m)

unionWith :: (Ord a, TreeOrdering t) =>
             (v -> v -> v) -> Map a t v -> Map a t v -> Map a t v
unionWith f (TM m) (TM n) = TM (M.unionWith f m n)
