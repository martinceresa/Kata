{-# LANGUAGE ScopedTypeVariables, Rank2Types #-}
module ScottEncoding where

import Prelude hiding (null, length, map, foldl, foldr, take, fst, snd, curry, uncurry, concat, zip, (++))

newtype SMaybe a = SMaybe { runMaybe :: forall b. b -> (a -> b) -> b }
newtype SList a = SList { runList :: forall b. b -> (a -> SList a -> b) -> b }
newtype SEither a b = SEither { runEither :: forall c. (a -> c) -> (b -> c) -> c }
newtype SPair a b = SPair { runPair :: forall c. (a -> b -> c) -> c }

toPair :: SPair a b -> (a,b)
toPair (SPair p) = p (\a b -> (a , b))
fromPair :: (a,b) -> SPair a b
fromPair (x, y) = SPair $ \f -> f x y

fst :: SPair a b -> a
fst p = runPair p $ (\a _ -> a)
snd :: SPair a b -> b
snd p = runPair p $ (\_ b -> b)
swap :: SPair a b -> SPair b a
swap p = SPair $ runPair p . flip
curry :: (SPair a b -> c) -> (a -> b -> c)
curry f a b =  f (fromPair (a , b))
uncurry :: (a -> b -> c) -> (SPair a b -> c)
uncurry f p = f (fst p) (snd p)

toMaybe :: SMaybe a -> Maybe a
toMaybe m = runMaybe m Nothing Just
fromMaybe :: Maybe a -> SMaybe a
fromMaybe m = maybe (SMaybe (\b _ -> b)) (\a -> SMaybe (\_ f -> f a)) m
isJust :: SMaybe a -> Bool
isJust m = runMaybe m False (const True)
isNothing :: SMaybe a -> Bool
isNothing m = runMaybe m True (const False)
catMaybes :: SList (SMaybe a) -> SList a
catMaybes mas = runList mas (SList (\b _ -> b)) (\ma res -> runMaybe ma (catMaybes res) (flip cons (catMaybes res)))

toEither :: SEither a b -> Either a b
toEither e = runEither e Left Right
fromEither :: Either a b -> SEither a b
fromEither = either (\a -> SEither (\l _ -> l a)) (\b -> SEither (\_ r -> r b))
isLeft :: SEither a b -> Bool
isLeft m = runEither m (const True) (const False)
isRight :: SEither a b -> Bool
isRight m = runEither m (const False) (const True)
partition :: SList (SEither a b) -> SPair (SList a) (SList b)
partition lrs = runList lrs (fromPair (fromList [],fromList []))
                (\x res ->
                   runEither x (\a -> appLeft (cons a) (partition res))
                               (\b -> appRight (cons b) (partition res))
                )
appLeft :: (a -> b) -> SPair a c -> SPair b c
appLeft f p = SPair $ \g -> runPair p (\a c -> g (f a) c)

appRight :: (a -> b) -> SPair c a -> SPair c b
appRight f p = SPair $ \g -> runPair p (\c a -> g c (f a))

toList :: SList a -> [a]
toList ls = runList ls [] (\a xs -> a : toList xs)
fromList :: [a] -> SList a
fromList [] = SList (\b _ -> b)
fromList (x:xs) = SList (\_ r -> r x (fromList xs))
cons :: a -> SList a -> SList a
cons a ls = SList (\_ r -> r a ls)
concat :: SList a -> SList a -> SList a
concat ls = runList ls id (\a res -> cons a . (concat res))

foldl :: (b -> a -> b) -> b -> SList a -> b
foldl fs fz ls = runList ls fz (\a res -> (foldl fs (fs fz a) res))

foldr :: (a -> b -> b) -> b -> SList a -> b
foldr fs fz ls = runList ls fz (\a res -> fs a (foldr fs fz res))
null :: SList a -> Bool
null ls = runList ls True (\_ _ -> False)
length :: SList a -> Int
length = foldr (\_ -> (1 +)) 0
map :: (a -> b) -> SList a -> SList b
map f = foldr (\a-> cons (f a)) (fromList [])
zip :: SList a -> SList b -> SList (SPair a b)
zip ls rs = runList ls (fromList []) -- ls empty list
            (\a resa -> -- ls is not empty
               runList rs (fromList []) -- but rs is empty
               (\b resb -> cons (fromPair (a,b)) (zip resa resb)) -- rs not empty
               )
take :: Int -> SList a -> SList a
take 0 ls = ls
take n ls = runList ls (fromList []) (\_ res -> take (n-1) res)
