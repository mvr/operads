import Math.Operad
import Data.List

a = corolla 1 [1,2]
b = corolla 2 [1,2]

la1 = shuffleCompose 1 [1,2,3] a a
la2 = shuffleCompose 1 [1,3,2] a a
la3 = shuffleCompose 2 [1,2,3] a a
         
lb1 = shuffleCompose 1 [1,2,3] b b
lb2 = shuffleCompose 1 [1,3,2] b b
lb3 = shuffleCompose 2 [1,2,3] b b
         
lc1 = shuffleCompose 1 [1,2,3] b a
lc2 = shuffleCompose 1 [1,3,2] b a
lc3 = shuffleCompose 2 [1,2,3] b a
         
ld1 = shuffleCompose 1 [1,2,3] a b
ld2 = shuffleCompose 1 [1,3,2] a b
ld3 = shuffleCompose 2 [1,2,3] a b

oa1 = oet la1 :: OperadElement Integer Rational RPathPerm
oa2 = oet la2 :: OperadElement Integer Rational RPathPerm
oa3 = oet la3 :: OperadElement Integer Rational RPathPerm
         
ob1 = oet lb1 :: OperadElement Integer Rational RPathPerm
ob2 = oet lb2 :: OperadElement Integer Rational RPathPerm
ob3 = oet lb3 :: OperadElement Integer Rational RPathPerm

oc1 = oet lc1 :: OperadElement Integer Rational RPathPerm
oc2 = oet lc2 :: OperadElement Integer Rational RPathPerm
oc3 = oet lc3 :: OperadElement Integer Rational RPathPerm

od1 = oet ld1 :: OperadElement Integer Rational RPathPerm
od2 = oet ld2 :: OperadElement Integer Rational RPathPerm
od3 = oet ld3 :: OperadElement Integer Rational RPathPerm


ra = oa1 - oa2 - oa3
rb = ob1 - ob2 - ob3

r1 = oc1 - oc2 - oc3
r2 = od1 - od2 - od3
r3 = oc1 - od1
r4 = oc2 - od2
r5 = oc3 - od3

gens = [ra,rb,r1,r2,r3,r4]
gb0 = gens
gbn0 = stepInitialOperadicBuchberger 4 [] gb0
gb1 = nub $ gb0 ++ gbn0
gbn1 = stepInitialOperadicBuchberger 4 gb0 gbn0
gb2 = nub $ gb1 ++ gbn1 
gbn2 = stepInitialOperadicBuchberger 4 gb1 gbn1


main = putStrLn . unlines . map pp $ gbn1