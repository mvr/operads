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

data (Ord a, Show a, TreeOrdering t) => StoredTree a t = ST [[a]] [Int] (OrderedTree a t) deriving (Show, Read, Eq)

sot :: (Ord a, Show a, TreeOrdering t) => OrderedTree a t -> StoredTree a t
sot pdt = let
    (path,perm) = orderedPathSequence (dt pdt)
  in ST path perm pdt

dot :: (Ord a, Show a, TreeOrdering t) => StoredTree a t -> OrderedTree a t
dot (ST _ _ pdt) = pdt

instance (Ord a, Show a, TreeOrdering t) => Ord (StoredTree a t) where
    compare (ST pathseq pathperm (OT t o)) (ST pathseq' pathperm' (OT s _)) = 
        comparePathSequence o t (pathseq,pathperm) s (pathseq', pathperm')

data (Ord a, Show a, TreeOrdering t) => Map a t v = TM (M.Map (StoredTree a t) v) deriving (Show, Read, Eq, Ord)

filter :: (Ord a, Show a, TreeOrdering t) => (v -> Bool) -> Map a t v -> Map a t v
filter f (TM m) = TM $ M.filter f m

foldWithKey :: (Ord a, Show a, TreeOrdering t) => 
               (OrderedTree a t -> v -> b -> b) -> b -> Map a t v -> b
foldWithKey f i (TM m) = M.foldWithKey (\k val acc -> f (dot k) val acc) i m

fromListWith :: (Ord a, Show a, TreeOrdering t) => 
                (v -> v -> v) -> [(OrderedTree a t, v)] -> Map a t v
fromListWith f lst = TM $ M.fromListWith f (P.map (first sot) lst)

intersectionWith :: (Ord a, Show a, TreeOrdering t) => 
                    (u -> v -> w) -> Map a t u -> Map a t v -> Map a t w
intersectionWith f (TM m) (TM n) = TM $ M.intersectionWith f m n

keys :: (Ord a, Show a, TreeOrdering t) => Map a t v -> [OrderedTree a t]
keys (TM m) = P.map dot . M.keys $ m

map :: (Ord a, Show a, TreeOrdering t) => 
       (v -> w) -> Map a t v -> Map a t w
map f (TM m) = TM $ M.map f m

mapKeysWith :: (Ord a, Show a, TreeOrdering t, Ord b, Show b, TreeOrdering s) => 
               (v -> v -> v) -> (OrderedTree a t -> OrderedTree b s) -> Map a t v -> Map b s v
mapKeysWith c f (TM m) = TM $ M.mapKeysWith c (sot . f . dot) m

maxViewWithKey :: (Ord a, Show a, TreeOrdering t) => 
                  Map a t v -> Maybe ((OrderedTree a t, v), Map a t v)
maxViewWithKey (TM m) = fmap (\((t,v),mmap) -> ((dot t, v), TM mmap)) . M.maxViewWithKey $ m

null :: (Ord a, Show a, TreeOrdering t) => Map a t v -> Bool
null (TM m) = M.null m 

toList :: (Ord a, Show a, TreeOrdering t) => Map a t v -> [(OrderedTree a t, v)]
toList (TM m) = P.map (first dot) (M.toList m)

unionWith :: (Ord a, Show a, TreeOrdering t) => 
             (v -> v -> v) -> Map a t v -> Map a t v -> Map a t v
unionWith f (TM m) (TM n) = TM (M.unionWith f m n)
