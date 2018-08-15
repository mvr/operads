-- Copyright 2009 Mikael Vejdemo Johansson <mik@stanford.edu>
-- Released under a BSD license

-- | Pretty printing for user interaction.

module Math.Operad.PPrint where

import Data.List (intercalate)

-- * Pretty printing

-- | This yields user interface functions for human readable printing of objects.
-- The idea is to use 'Show' instances for marshalling of data, and 'PPrint' for
-- user interaction.
class PPrint a where
    pp :: a -> String
    pP :: a -> IO ()
    pP = putStrLn . pp

instance (PPrint a) => PPrint [a] where
    pp rs = "[" ++ (unlines . map ((++",") . pp) $ rs) ++ "]"

instance (PPrint a, PPrint b) => PPrint (a,b) where
    pp (r,t) = "(" ++ (intercalate "," [pp r, pp t]) ++ ")"

instance (PPrint a, PPrint b, PPrint c) => PPrint (a,b,c) where
    pp (r,s,t) = "(" ++ (intercalate "," [pp r, pp s, pp t]) ++ ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d) => PPrint (a,b,c,d) where
    pp (r,s,t,u) = "(" ++ (intercalate "," [pp r, pp s, pp t, pp u]) ++ ")"

instance (PPrint a, PPrint b, PPrint c, PPrint d, PPrint e) => PPrint (a,b,c,d,e) where
    pp (r,s,t,u,v) = "(" ++ (intercalate "," [pp r, pp s, pp t, pp u, pp v]) ++ ")"

instance PPrint Int where
    pp i = show i

instance PPrint Integer where
    pp i = show i

instance (PPrint a) => PPrint (Maybe a) where
    pp Nothing = "Nothing"
    pp (Just a) = "Just " ++ pp a

instance (PPrint a, PPrint b) => PPrint (Either a b) where
    pp (Left a) = "Left " ++ pp a
    pp (Right a) = "Right " ++ pp a