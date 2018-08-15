-- Copyright 2009 Mikael Vejdemo Johansson <mik@stanford.edu>
-- Released under a BSD license

module Math.Operad (module Math.Operad.PPrint, 
                    module Math.Operad.MapOperad,
                    module Math.Operad.OrderedTree,
                    module Math.Operad.OperadGB,
                    m12_3,
                    m13_2,
                    m1_23,
                    m2,
                    m3,
                    yTree,
                    lgb, 
                    Tree, 
                    FreeOperad) where

import Math.Operad.OperadGB
import Math.Operad.OrderedTree
import Math.Operad.PPrint
import Math.Operad.MapOperad

type Tree = DecoratedTree Integer
type FreeOperad a = OperadElement a Rational PathPerm

-- ** Examples and useful predefined operad elements.

-- | The element m2(m2(1,2),3)
m12_3 :: DecoratedTree Integer
m12_3 = symmetricCompose 1 [1,2,3] (corolla 2 [1,2]) (corolla 2 [1,2])

-- | The element m2(m2(1,3),2)
m13_2 :: DecoratedTree Integer
m13_2 = symmetricCompose 1 [1,3,2] (corolla 2 [1,2]) (corolla 2 [1,2])

-- | The element m2(1,m2(2,3))
m1_23 :: DecoratedTree Integer
m1_23 = symmetricCompose 2 [1,2,3] (corolla 2 [1,2]) (corolla 2 [1,2])

-- | The element m2(1,2)
m2 :: DecoratedTree Integer
m2 = corolla 2 [1,2] 

-- | The element m3(1,2,3)
m3 :: DecoratedTree Integer
m3 = corolla 3 [1,2,3]

-- | The element m2(m2(1,2),m2(3,4))
yTree :: DecoratedTree Integer
yTree = nsCompose 1 (nsCompose 2 m2 m2) m2

-- The Lie operad example computation

lo1 :: OperadElement Integer Rational PathPerm
lo1 = oet m12_3

lo2 :: OperadElement Integer Rational PathPerm
lo2 = oet m13_2

lo3 :: OperadElement Integer Rational PathPerm
lo3 = oet m1_23

-- | The list of operad elements consisting of 'm12_3'-'m13_2'-'m1_23'. This generates the 
-- ideal of relations for the operad Lie.
lgb :: [OperadElement Integer Rational PathPerm]
lgb = [lo1 - lo2 - lo3]

