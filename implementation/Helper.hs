module Helper where

remDup :: (Eq a) => [a] -> [a]
remDup [] = []
remDup (x : xs) = x : filter (/= x) (remDup xs)

findIndex :: Eq a => a -> [a] -> Int
findIndex x [] = -1
findIndex x (v:vs) | v == x = 0
                    | otherwise = if ind == -1 then -1 else 1 + ind
                                    where
                                        ind = findIndex x vs

isNothing :: Maybe a -> Bool
isNothing Nothing = True
isNothing _ = False

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust _ = False

just :: Maybe a -> a 
just (Just x) = x 

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

left :: Either a b -> a
left (Left x) = x 

right :: Either a b -> b 
right (Right y) = y

class Pretty a where
    pretty :: a -> String

instance Pretty String where
    pretty = id

instance Pretty Int where
    pretty = show
