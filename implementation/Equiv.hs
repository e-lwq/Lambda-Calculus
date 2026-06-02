module Equiv where

import Basic
import Helper
import Data.Bool (Bool)
import Data.Maybe (Maybe(Nothing))

data DBTerm a = Bounded' Int | Free' a | App' (DBTerm a) (DBTerm a) | Abs' (DBTerm a)
  deriving (Eq,Show)

-- convert LambdaTerm to one using partial de brujin indices
convert :: (Eq a) => [a] -> LambdaTerm a -> DBTerm a
convert bs (Var x)
  | ind == -1 = Free' x
  | otherwise = Bounded' ind
  where
    ind = findIndex x bs
convert bs (App m n) = App' (convert bs m) (convert bs n)
convert bs (Abs x m) = Abs' (convert (x : bs) m)

alphaEquiv :: (Eq a) => LambdaTerm a -> LambdaTerm a -> Bool
alphaEquiv m n = convert [] m == convert [] n

betaReduce' :: (Eq a) => a -> LambdaTerm a -> LambdaTerm a -> LambdaTerm a
betaReduce' x m n = substitute m x n

betaReduce :: (Eq a) => LambdaTerm a -> LambdaTerm a
betaReduce (App (Abs x m) n) = betaReduce' x m n

isRedex :: LambdaTerm a -> Bool
isRedex (App (Abs _ _) _) = True
isRedex _ = False

hasRedex :: (Eq a) => LambdaTerm a -> Bool
hasRedex m = any isRedex (subTerms m)

isBetaNF :: (Eq a) => LambdaTerm a -> Bool
isBetaNF = not . hasRedex

possibleSteps :: (Eq a) => LambdaTerm a -> [LambdaTerm a]
possibleSteps (Var _) = []
possibleSteps (App (Abs x m) n) = betaReduce' x m n : map (\l -> App (Abs x l) n) (possibleSteps m) ++ map (App (Abs x m)) (possibleSteps n)
possibleSteps (App m n) = map (`App` n) (possibleSteps m) ++ map (App m) (possibleSteps n)
possibleSteps (Abs x m) = map (Abs x) (possibleSteps m)

eagereval :: (Eq a) => (LambdaTerm a -> [LambdaTerm a]) -> (LambdaTerm a -> Bool) -> [LambdaTerm a] -> LambdaTerm a 
eagereval evalone finish ms = if isJust ff then just ff 
                              else eagereval evalone finish (concatMap evalone ms)
                              where
                                ff = findfinish ms
                                
                                findfinish [] = Nothing
                                findfinish (x:xs) = if finish x then Just x else findfinish xs 

eval :: (Eq a) => (LambdaTerm a -> [LambdaTerm a]) -> (LambdaTerm a -> Bool) -> LambdaTerm a -> LambdaTerm a
eval evalone finish m = if finish m then m
                        else eagereval evalone finish (evalone m)

findBetaNF :: (Eq a) => LambdaTerm a -> LambdaTerm a 
findBetaNF = eval possibleSteps isBetaNF

beta1Reductible :: (Eq a) => LambdaTerm a -> LambdaTerm a -> Bool
beta1Reductible m n = any (`alphaEquiv` n) (possibleSteps m)

betaReductible :: (Eq a) => LambdaTerm a -> LambdaTerm a -> Bool
betaReductible m n = eval possibleSteps p m `alphaEquiv` n 
                where
                  p x = isBetaNF x || x `alphaEquiv` n

betaEquiv :: (Eq a) => LambdaTerm a -> LambdaTerm a -> Bool
betaEquiv m n = findBetaNF m `alphaEquiv` findBetaNF n


term1 = App (Abs "w" (App (Abs "y" (Var "y")) (Var "w"))) (Var "v")
term2 = App (Abs "x" (Var "x")) (Var "v")
term3 = App (Abs "y" (Var "y")) (Var "v")
term4 = Var "v"
term5 = Var "x"