import Test.QuickCheck
import Text.Printf
import Data.List (sort, nub)
import Data.Ord
import Control.Monad

import Math.Operad.OperadGB
import Math.Operad.PPrint
import Math.Operad.MapOperad
import Math.Operad.OrderedTree

main = mapM_ (\(s,a) -> printf "%-25s: " s >> a) tests

newtype Tree = Tree (DecoratedTree Int) deriving (Ord, Eq, Show, Read)

instance PPrint Tree where
    pp (Tree t) = pp t

-- The paper examples for the PathPerm ordering
(.>.) s t = GT == (treeCompare PathPerm s t)

l1 = symmetricCompose 1 [1,2,3] (corolla 6 [1,2]) (corolla 5 [1,2])
l2 = symmetricCompose 1 [1,2,3] (corolla 3 [1,2]) (corolla 2 [1,2])
l3 = symmetricCompose 1 [1,2,3] (corolla 3 [1,2]) (corolla 2 [1,2])
l4 = symmetricCompose 1 [1,2,3] (corolla 2 [1,2]) (corolla 2 [1,2])
r1 = symmetricCompose 1 [1,3,2] (corolla 3 [1,2]) (corolla 2 [1,2])
r2 = symmetricCompose 1 [1,3,2] (corolla 3 [1,2]) (corolla 2 [1,2])
r3 = symmetricCompose 1 [1,3,2] (corolla 3 [1,2]) (corolla 2 [1,2])
r4 = symmetricCompose 1 [1,3,2] (corolla 3 [1,2]) (corolla 2 [1,2])

prop_paperpathlex1 = l1 .>. r1
prop_paperpathlex2 = l2 .>. r2
prop_paperpathlex3 = l3 .>. r3


prop_anticom = let
    v = corolla 2 [1,2]
    g1t1 = nsCompose 1 v v
    g1t2 = nsCompose 2 v v
    g2t2 = shuffleCompose 1 [1,3,2] v v
    g1 = (oet g1t1) + (oet g1t2) :: OperadElement Integer Rational PathPerm
    g2 = (oet g2t2) - (oet g1t2) :: OperadElement Integer Rational PathPerm
    ac = [g1,g2]
    acGB = operadicBuchberger ac
  in ((3==) . length $ acGB) &&
     (sort acGB) == (sort . read $ "[OE (TM (fromList [(ST [[2],[2,2],[2,2]] [1,2,3] (OT (DTVertex {vertexType = 2, subTrees = [DTLeaf 1,DTVertex {vertexType = 2, subTrees = [DTLeaf 2,DTLeaf 3]}]}) PathPerm),(-1) % 1),(ST [[2,2],[2],[2,2]] [1,3,2] (OT (DTVertex {vertexType = 2, subTrees = [DTVertex {vertexType = 2, subTrees = [DTLeaf 1,DTLeaf 3]},DTLeaf 2]}) PathPerm),1 % 1)])),OE (TM (fromList [(ST [[2],[2,2],[2,2]] [1,2,3] (OT (DTVertex {vertexType = 2, subTrees = [DTLeaf 1,DTVertex {vertexType = 2, subTrees = [DTLeaf 2,DTLeaf 3]}]}) PathPerm),1 % 1),(ST [[2,2],[2,2],[2]] [1,2,3] (OT (DTVertex {vertexType = 2, subTrees = [DTVertex {vertexType = 2, subTrees = [DTLeaf 1,DTLeaf 2]},DTLeaf 3]}) PathPerm),1 % 1)])),OE (TM (fromList [(ST [[2],[2,2],[2,2,2],[2,2,2]] [1,2,3,4] (OT (DTVertex {vertexType = 2, subTrees = [DTLeaf 1,DTVertex {vertexType = 2, subTrees = [DTLeaf 2,DTVertex {vertexType = 2, subTrees = [DTLeaf 3,DTLeaf 4]}]}]}) PathPerm),2 % 1)]))]" :: [OperadElement Integer Rational PathPerm])

     
prop_noncom = let
    x = corolla 1 [1]
    y = corolla 2 [1]
    x2y = nsCompose 1 x (nsCompose 1 x y)
    xy2 = nsCompose 1 x (nsCompose 1 y y)
    xy = nsCompose 1 x y
    yx = nsCompose 1 y x
    one = head $ subTrees x
    ox2y = oet x2y  :: OperadElement Integer Rational PathPerm
    oxy2 = oet xy2  :: OperadElement Integer Rational PathPerm
    oxy = oet xy  :: OperadElement Integer Rational PathPerm
    oyx = oet yx  :: OperadElement Integer Rational PathPerm
    oone = oet one  :: OperadElement Integer Rational PathPerm
    gb = [ox2y-oone, oxy2-oone, oxy-oyx]
  in (sort . operadicBuchberger $ gb) == (sort . read $ "[OE (TM (fromList [(ST [[1]] [1] (OT (DTVertex {vertexType = 1, subTrees = [DTLeaf 1]}) PathPerm),(-1) % 1),(ST [[2]] [1] (OT (DTVertex {vertexType = 2, subTrees = [DTLeaf 1]}) PathPerm),1 % 1)])),OE (TM (fromList [(ST [[]] [1] (OT (DTLeaf 1) PathPerm),(-1) % 1),(ST [[1,1,1]] [1] (OT (DTVertex {vertexType = 1, subTrees = [DTVertex {vertexType = 1, subTrees = [DTVertex {vertexType = 1, subTrees = [DTLeaf 1]}]}]}) PathPerm),1 % 1)]))]" :: [OperadElement Integer Rational PathPerm])


prop_preliekoszul = let
    a = corolla 2 [1,2]
    b = corolla 1 [1,2]

    t1 = shuffleCompose 1 [1,2,3] a a
    t2 = shuffleCompose 2 [1,2,3] a a
    t3 = shuffleCompose 1 [1,3,2] a a
    t4 = shuffleCompose 2 [1,2,3] a b

    t5 = shuffleCompose 1 [1,2,3] a b
    t6 = shuffleCompose 1 [1,3,2] b a
    t7 = shuffleCompose 2 [1,2,3] b a
    t8 = shuffleCompose 1 [1,3,2] b b

    t9 = shuffleCompose 1 [1,3,2] a b
    ta = shuffleCompose 1 [1,2,3] b a
    tb = shuffleCompose 2 [1,2,3] b b
    tc = shuffleCompose 1 [1,2,3] b b

    g1 = (oet t1 ) - (oet t2 ) - (oet t3 ) + (oet t4 ) :: OperadElement Integer Rational PathPerm
    g2 = (oet t5 ) - (oet t6 ) - (oet t7 ) + (oet t8 ) :: OperadElement Integer Rational PathPerm
    g3 = (oet t9 ) - (oet ta ) - (oet tb ) + (oet tc ) :: OperadElement Integer Rational PathPerm

    pl = [g1, g2, g3]
    plGB = operadicBuchberger pl
  in (length plGB == 3) && (([2]==) . sort . nub $ concatMap operationDegrees plGB)

prop_prelie = let
    a = corolla 1 [1,2]
    b = corolla 2 [1,2]

    t1 = shuffleCompose 1 [1,2,3] a a
    t2 = shuffleCompose 2 [1,2,3] a a
    t3 = shuffleCompose 1 [1,3,2] a a
    t4 = shuffleCompose 2 [1,2,3] a b

    t5 = shuffleCompose 1 [1,2,3] a b
    t6 = shuffleCompose 1 [1,3,2] b a
    t7 = shuffleCompose 2 [1,2,3] b a
    t8 = shuffleCompose 1 [1,3,2] b b

    t9 = shuffleCompose 1 [1,3,2] a b
    ta = shuffleCompose 1 [1,2,3] b a
    tb = shuffleCompose 2 [1,2,3] b b
    tc = shuffleCompose 1 [1,2,3] b b

    g1 = (oet t1 ) - (oet t2 ) - (oet t3 ) + (oet t4 ) :: OperadElement Integer Rational PathPerm
    g2 = (oet t5 ) - (oet t6 ) - (oet t7 ) + (oet t8 ) :: OperadElement Integer Rational PathPerm
    g3 = (oet t9 ) - (oet ta ) - (oet tb ) + (oet tc ) :: OperadElement Integer Rational PathPerm

    pl = [g1, g2, g3]
    plGB = operadicBuchberger pl
  in (length plGB == 16) && (([2..6]==) . sort . nub $ concatMap operationDegrees plGB)


tests = [
        ("Paper example 1 for PathPerm ordering",test prop_paperpathlex1),
        ("Paper example 2 for PathPerm ordering",test prop_paperpathlex1),
        ("Paper example 3 for PathPerm ordering",test prop_paperpathlex1),
        ("Anticommutative has 3 element basis",test prop_anticom),
        --("Pre-Lie with the wrong order",test prop_prelie),
        ("Pre-Lie is Koszul",test prop_preliekoszul),
        ("Sample non-commutative algebra grobner basis",test prop_noncom)
        ]
