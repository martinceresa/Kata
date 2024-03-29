{-# LANGUAGE 
  FlexibleInstances, 
  UndecidableInstances, 
  InstanceSigs,
  ScopedTypeVariables,
  RankNTypes #-}

module PC where

import Data.List

type ISO a b = (a -> b, b -> a)
-- See https://www.codewars.com/kata/isomorphism

symm :: ISO a b -> ISO b a
symm (ab, ba) = (ba, ab)

substL :: ISO a b -> (a -> b)
substL = fst

substR :: ISO a b -> (b -> a)
substR = snd

liftISO2 :: ISO a b -> ISO (a -> a -> a) (b -> b -> b)
liftISO2 (ab , ba) = (\faaa p q -> ab $ faaa (ba p) (ba q)
                     ,\g p q  -> ba $ g (ab p) (ab q))

-- A Natural Number is either Zero,
-- or a Successor (1 +) of Natural Number.
-- We have (+)/(*) on Natural Number, or (-) it.
-- Since Natrual Number do not have negative, forall x, 0 - x = 0.
-- We also have pow on Natrual Number
-- Since Haskell is lazy, we also have infinity

class Nat n where
  zero :: n
  successor :: n -> n
  nat :: a -> (n -> a) -> n -> a -- Pattern Matching
  iter :: a -> (a -> a) -> n -> a -- Induction
  plus, minus, mult, pow :: n -> n -> n
  inf :: n
  inf = successor inf
  divide :: n -> n -> n
  l `divide` r | l == 0 && r == 0 = undefined
  l `divide` r | l < r = 0
  l `divide` r | otherwise = successor $ (l `minus` r) `divide` r
  -- notice (l `divide` 0) when l is not 0 will return inf
  isoP :: ISO n Peano -- See below for the definition of Peano
  isoP = (iter zero successor, iter zero successor)
  toP :: n -> Peano
  toP = substL isoP

instance {-# OVERLAPPABLE #-} Nat n => Show n where
  show = show . toP

instance {-# OVERLAPPABLE #-} Nat n => Eq n where
  l == r = toP l == toP r

instance {-# OVERLAPPABLE #-} Nat n => Ord n where
  l `compare` r = toP l `compare` toP r

instance {-# OVERLAPPABLE #-} Nat n => Num n where
  abs = id
  signum = nat zero (const 1)
  fromInteger 0 = zero
  fromInteger n | n > 0 = successor $ fromInteger (n - 1)
  (+) = plus
  (*) = mult
  (-) = minus

-- We can encode Natrual Number directly as Algebraic Data Type(ADT).
data Peano = O | S Peano deriving (Show, Eq, Ord)

-- Remember, 0 - x = 0 for all x.
pred :: Peano -> Peano
pred = nat O id
instance Nat Peano where
  zero = O
  successor = S
  nat cz _ O = cz
  nat _ cs (S n) = cs n
  iter cz _ O = cz
  iter cz cs (S n) = cs (iter cz cs n)
  plus n = iter id (successor .) n
  minus n m = (iter id (\f -> nat zero f ) m) n
  mult n = iter zero (plus n)
  pow n = iter (successor zero) (mult n)

-- Peano is very similar to a basic data type in Haskell - List!
-- O is like [], and S is like :: (except it lack the head part)
-- When we want to store no information, we can use (), a empty tuple
-- This is different from storing nothing (called Void in Haskell),
-- as we can create a value of () by using (), 
-- but we cannot create a value of Void.

-- Notice how you can implement everything once you have isoP,
-- By converting to Peano and using Nat Peano?
-- Dont do that. You wont learn anything.
-- Try to use operation specific to list.
instance Nat [()] where
  zero = []
  successor = (():)
  nat cz _ [] = cz
  nat _ cs (_ : xs) = cs xs
  iter  cz cs = foldr (\_ c -> cs c ) cz
  plus n = iter id (successor .) n
  minus n m = (iter id (\f -> nat zero f ) m) n
  mult n = iter zero (plus n)
  pow n = iter (successor zero) (mult n)

-- Instead of defining Nat from zero, sucessor (and get Peano),
-- We can define it from Pattern Matching
newtype Scott = Scott { runScott :: forall a. a -> (Scott -> a) -> a }
instance Nat Scott where
  -- Other operation on Scott numeral is sort of boring,
  -- So we implement it using operation on Peano.
  -- You shouldnt do this - I had handled all the boring case for you.
  plus = substR (liftISO2 isoP) plus
  minus = substR (liftISO2 isoP) minus
  mult = substR (liftISO2 isoP) mult
  pow = substR (liftISO2 isoP) pow
  zero = Scott $ \ z _ -> z
  successor n = Scott $ \ _ s -> s n
  nat cz cn n = runScott n cz cn
  iter cz zs = nat cz (zs . iter cz zs)

-- Or from induction!
newtype Church = Church { runChurch :: forall a. (a -> a) -> a -> a }
instance Nat Church where
  -- Try to implement the calculation (except minus) in the primitive way.
  -- Implement them by constructing Church explicitly.
  -- So plus should not use successor,
  -- mult should not use plus,
  -- exp should not use mult.
  zero = Church $ \_ z -> z
  successor n = Church $ \s z -> s $ runChurch n s z
  iter cz cs n = runChurch n cs cz
  nat cz cs n = runChurch n (\_ -> cs
                                   (fst $ runChurch n (\(_,p) -> (p , successor p)) (zero, zero)) -- Pred
                            ) cz
  minus n m = (iter id (\f -> nat zero f ) m) n
  plus = iter id (\f n -> Church $ \s z -> s (runChurch (f n) s z))
  mult = iter (\_ -> zero) (\f n -> Church $ \s z -> runChurch n s (runChurch (f n) s z))
  pow m = iter (successor zero) (\p -> _)
    --Church $ runChurch n (runChurch m) (\f s -> f s)

