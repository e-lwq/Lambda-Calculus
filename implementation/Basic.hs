module Basic where

import Helper  

data LambdaTerm t = Var t | App (LambdaTerm t) (LambdaTerm t) | Abs t (LambdaTerm t) 
    deriving (Eq, Show)

type Var = String

syntaxEquiv :: LambdaTerm Var -> LambdaTerm Var -> Bool
syntaxEquiv (Var t1) (Var t2) = t1==t2
syntaxEquiv (App m1 n1) (App m2 n2) = syntaxEquiv m1 m1 && syntaxEquiv n1 n2
syntaxEquiv (Abs x1 m1) (Abs x2 m2) = x1==x2 && syntaxEquiv m1 m2
syntaxEquiv _ _ = False

subTerms :: LambdaTerm a -> [LambdaTerm a]
subTerms (Var v) = [Var v]
subTerms (App m n) = App m n : subTerms m ++ subTerms n
subTerms (Abs x m) = Abs x m : subTerms m

isSubTerm :: Eq a => LambdaTerm a -> LambdaTerm a -> Bool
isSubTerm m' m = m' `elem` subTerms m

isProperSubterm :: Eq a => LambdaTerm a -> LambdaTerm a -> Bool
isProperSubterm m' m = m' /= m && isSubTerm m' m

freeVar' :: Eq a => LambdaTerm a -> [a]
freeVar' (Var v) = [v]
freeVar' (App m n) = freeVar' m ++ freeVar' n
freeVar' (Abs x m) = filter (/=x) (freeVar' m)

freeVar :: Eq a => LambdaTerm a -> [a]
freeVar = remDup . freeVar'

boundedVar' :: LambdaTerm a -> [a]
boundedVar' (Var v) = []
boundedVar' (App m n) = boundedVar' m ++ boundedVar' n
boundedVar' (Abs x m) = x : boundedVar' m

boundedVar :: Eq a => LambdaTerm a -> [a]
boundedVar = remDup . boundedVar'

allVar :: Eq a => LambdaTerm a -> [a]
allVar m = remDup (freeVar' m ++ boundedVar' m)

isClosed :: Eq a => LambdaTerm a -> Bool
isClosed m = null (freeVar m)

rename :: Eq a => LambdaTerm a -> a -> a -> LambdaTerm a
rename (Var v) x y = if v == x then Var y else Var v
rename (App m n) x y = App (rename m x y) (rename n x y)
rename (Abs v m) x y = if v == x then Abs v m else Abs v (rename m x y)

substitute :: Eq a => LambdaTerm a -> a -> LambdaTerm a -> LambdaTerm a
substitute (Var v) x n = if v == x then n else Var v
substitute (App m1 m2) x n = App (substitute m1 x n) (substitute m2 x n)
substitute (Abs v m) x n = if v == x then Abs v m else Abs v (substitute m x n)
