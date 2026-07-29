module Typed where

import Helper 
import Data.Char (ord,chr)

type V = Int
data T = V V | To T T deriving Eq

isV (V _) = True
isV _ = False

getT2 :: T -> T
getT2 (To _ t) = t

instance Show T where
    show (V n) = "t" ++ show n
    show (To a b) = pl ++ show a ++ pr ++ "->" ++ show b
        where 
            (pl,pr) = if isV a then ("","") else ("(",")")

data Pretyped a = PVar a | PApp (Pretyped a) (Pretyped a) | PAbs a T (Pretyped a)
    deriving Eq

isPAbs (PAbs _ _ _) = True
isPAbs _ = False

isPApp (PApp _ _) = True
isPApp _ = False

isPVar (PVar _) = True
isPVar _ = False

instance Functor Pretyped where
    fmap f (PVar a) = PVar (f a)
    fmap f (PApp m n) = PApp (fmap f m) (fmap f n)
    fmap f (PAbs x a m) = PAbs (f x) a (fmap f m)

instance Show a => Show (Pretyped a) where
    show (PVar a) = show a
    show (PApp m n) = pml ++ show m ++ pmr ++ " " ++ pnl ++ show n ++ pnr 
                    where
                        (pml,pmr) = if isPAbs m then ("(",")") else ("","")
                        (pnl,pnr) = if isPVar n then ("","") else ("(",")")
    show (PAbs x t m) = "\\" ++ show x ++ " : " ++ show t ++ ". " ++ show m  

type Declaration a = (a , T)
disp :: Show a => Declaration a -> String
disp (x, t) = show x ++ " : " ++ show t

type Context a = [Declaration a]
data Judgement a = J {context :: Context a, term :: Pretyped a, ptype :: T}

matchAppl :: T -> T -> Bool
matchAppl (To t1 t2) t3 = t3==t1
matchAppl _ _ = False

findPair :: Eq a => a -> Context a -> Maybe T
findPair x [] = Nothing
findPair x ((y,t):ts) | x==y = Just t
                        | otherwise = findPair x ts 

findType :: Eq a => Context a -> Pretyped a -> Maybe (Judgement a)
findType context (PAbs x t m) | isNothing fm = Nothing
                                | otherwise = Just (J context (PAbs x t m) (To t (ptype (just fm))))
                                    where
                                        fm = findType ((x,t):context) m 
findType context (PApp m n) | isNothing fm || isNothing fn = Nothing
                                | not (matchAppl (ptype (just fm)) (ptype (just fn))) = Nothing
                                | otherwise = Just (J context (PApp m n) (getT2 (ptype (just fm))))
                                where
                                    fm = findType context m 
                                    fn = findType context n 
findType context (PVar x) | isNothing fx = Nothing
                                | otherwise = Just (J context (PVar x) (just fx))
                                    where
                                        fx = findPair x context

instance Show a => Show (Judgement a) where
    show (J c t p) = unlines (map disp c) ++ "=> " ++ show t ++ " : " ++ show p ++ "\n"

isDerivableJudgement :: Eq a => Judgement a -> Bool
isDerivableJudgement (J c m t) = isJust fj && ptype (just fj) == t
                            where
                                fj = findType c m

-- assume n does not have free variables bounded in m
subTyped :: Eq a => Pretyped a -> a -> Pretyped a -> Pretyped a
subTyped (PVar v) x n | v==x = n 
                        | otherwise = PVar v 
subTyped (PApp m l) x n = PApp (subTyped m x n) (subTyped l x n)
subTyped (PAbs y t m) x n | y == x = PAbs y t m
                            | otherwise = PAbs y t (subTyped m x n)

--betaReduceTyped' :: Eq a => a -> T -> Pretyped a -> Pretyped a -> Pretyped a
--betaReduceTyped' x t m n = subTyped m x n  

--betaReduceTyped :: Eq a => Pretyped a -> Pretyped a -> Pretyped a 
--betaReduceTyped (PAbs x t m) n = betaReduceTyped' x t m n

betaReduceTypes :: T -> T -> T 
betaReduceTypes (To a b) c | a==c = b

-- assume can always successfully find
find :: (Eq a) => T -> [(Pretyped a, T)] -> Maybe (Pretyped a, T)
find t cs | isNothing fp = if bcs == cs then Nothing else find t bcs
            | otherwise = fp
            where
                fp = findPTPair t cs
                bcs = bfsstep cs

findPTPair :: (Eq a) => T -> [(Pretyped a, T)] -> Maybe (Pretyped a, T)
findPTPair t [] = Nothing
findPTPair t ((m,t'):ds) | t == t' = Just (m,t')
                        | otherwise = findPTPair t ds

bfsstep' :: (Eq a) => [(Pretyped a, T)] -> [(Pretyped a, T)]
bfsstep' ds = concat [applyone p ds | p <- ds]

bfsstep :: (Eq a) => [(Pretyped a, T)] -> [(Pretyped a, T)]
bfsstep ds = ds ++ bfsstep' ds

applyone :: (Eq a) => (Pretyped a, T) -> [(Pretyped a, T)] -> [(Pretyped a, T)]
applyone (m, t) [] = []
applyone (m,t) ((m',t'):ds) | matchAppl t t' = (PApp m m', betaReduceTypes t t')  : applyone (m,t) ds
                            | otherwise = applyone (m,t) ds

-- find term matching type with given context, no free variables allowed
termFindingInt :: [(Pretyped Int, T)] -> T -> Maybe (Pretyped Int)
termFindingInt c (V v) = if isNothing fv then Nothing else Just (fst (just fv))
                            where fv = find (V v) c
termFindingInt c (To a b) =  if isNothing fv then Nothing else Just (PAbs x a (just fv))
                        where
                            fv = termFindingInt ((PVar x,a):c) b
                            x = length c

convertIntToString :: Pretyped Int -> Pretyped String
convertIntToString = fmap tostr
    where
        tostr n = [chr (ord 'A' + n)]

termFinding :: T -> Maybe (Pretyped String)
termFinding t = if isNothing tf then Nothing else fmap convertIntToString tf 
        where
            tf = termFindingInt [] t

type1 = To (To (V 1) (To (V 1) (V 3))) (To (V 1) (To (V 2) (V 3)))
type2 = To (To (To (V 1) (V 3)) (V 1)) (To (To (V 1) (V 3)) (To (V 2) (V 3)))
type3 = To (To (To (V 1) (V 2)) (V 1)) (To (To (V 1) (To (V 1) (V 2))) (V 1))
