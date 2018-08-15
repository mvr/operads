import Math.Operad

a = corolla 1 [1,2]
b = corolla 2 [1,2]

aa123 = nsCompose 1 a a
a1a23 = nsCompose 2 a a
aa132 = shuffleCompose 1 [1,3,2] a a

ab123 = nsCompose 1 a b
a1b23 = nsCompose 2 a b
ab132 = shuffleCompose 1 [1,3,2] a b

ba123 = nsCompose 1 b a
b1a23 = nsCompose 2 b a
ba132 = shuffleCompose 1 [1,3,2] b a

bb123 = nsCompose 1 b b
b1b23 = nsCompose 2 b b
bb132 = shuffleCompose 1 [1,3,2] b b

oaa123 = oet aa123 :: FreeOperad Integer
oab123 = oet ab123 :: FreeOperad Integer
oba123 = oet ba123 :: FreeOperad Integer
obb123 = oet bb123 :: FreeOperad Integer

oa1a23 = oet a1a23 :: FreeOperad Integer
oa1b23 = oet a1b23 :: FreeOperad Integer
ob1a23 = oet b1a23 :: FreeOperad Integer
ob1b23 = oet b1b23 :: FreeOperad Integer

oaa132 = oet aa132 :: FreeOperad Integer
oab132 = oet ab132 :: FreeOperad Integer
oba132 = oet ba132 :: FreeOperad Integer
obb132 = oet bb132 :: FreeOperad Integer

r1 = oaa123 - oa1a23 + oaa132 - oa1b23
r2 = oaa123 - oa1a23 + ob1b23 - obb123
r3 = oaa123 - oa1a23 + oab123 - oba132
r4 = oaa123 - oa1a23 - ob1a23 + obb132
r5 = oaa123 - oa1a23 - oab132 + oba123

gens = [r1,r2,r3,r4,r5]

main = putStrLn . show $ operadicBuchberger gens