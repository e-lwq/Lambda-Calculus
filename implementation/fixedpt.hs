module FixedPt where

import Basic

fixedPt :: LambdaTerm String -> LambdaTerm String
fixedPt l = App m m 
            where
                m = Abs "var" (App l (App (Var "var") (Var "var")))