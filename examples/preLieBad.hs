import Math.Operad 

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

g1 = (oet t1) - (oet t2) - (oet t3) + (oet t4) :: OperadElement Integer Rational PathPerm
g2 = (oet t5) - (oet t6) - (oet t7) + (oet t8) :: OperadElement Integer Rational PathPerm
g3 = (oet t9) - (oet ta) - (oet tb) + (oet tc) :: OperadElement Integer Rational PathPerm

pl0 = [g1, g2, g3]
pln0 = stepOperadicBuchberger [] pl0
pl1 = pl0 ++ pln0
pln1 = stepOperadicBuchberger pl0 pln0
pl2 = pl1 ++ pln1 

main = do 
  putStr . show $ length (take 25 pln1)
