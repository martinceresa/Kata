{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, UndecidableInstances #-}

module Kata.TimesComm where

-- import Kata.TimesComm.Definitions

{- Preloaded code. Maybe helpful for local editing. -}

-- | The natural numbers, encoded in types.
data Z
data S n

-- | Predicate describing natural numbers.
-- | This allows us to reason with `Nat`s.
data Natural :: * -> * where
  NumZ :: Natural Z
  NumS :: Natural n -> Natural (S n)

-- | Predicate describing equality of natural numbers.
data Equal :: * -> * -> * where
  EqlZ :: Equal Z Z
  EqlS :: Equal n m -> Equal (S n) (S m)

-- | Peano definition of addition.
type family (:+:) (n :: *) (m :: *) :: *
type instance Z :+: m = m
type instance S n :+: m = S (n :+: m)

-- | Peano definition of multiplication.
type family (:*:) (n :: *) (m :: *) :: *
type instance Z :*: m = Z
type instance S n :*: m = m :+: (n :*: m)

reflexivity :: Natural a -> Equal a a
reflexivity NumZ = EqlZ
reflexivity (NumS n) = EqlS $ reflexivity n

-- This will be helpful
plus' :: Equal n m -> Natural a -> Equal (n :+: a) (m :+: a)
plus' EqlZ m = reflexivity m
plus' (EqlS n) m = EqlS $ plus' n m

-- | Plus definition. It helps as evidence for reflexivity.
plus :: Natural a -> Natural b -> Natural (a :+: b)
plus NumZ b = b
plus (NumS a) b = NumS $ plus a b

-- This is the proof that the kata requires.
-- | a + (b + c) = (a + b) + c
plusAssoc :: Natural a -> Natural b -> Natural c -> Equal (a :+: (b :+: c)) ((a :+: b) :+: c)
plusAssoc NumZ a b = reflexivity $ plus a b
plusAssoc (NumS n) a b = EqlS $ plusAssoc n a b

-- | You need this! Copy your solution from
-- https://www.codewars.com/kata/a-plus-b-equals-b-plus-a-prove-it/haskell
-- plusComm :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
-- plusComm = undefined
-- | if a = b, then b = a.
symmetric :: Equal a b -> Equal b a
symmetric EqlZ = EqlZ
symmetric (EqlS n) = EqlS (symmetric n)

-- | if a = b and b = c, then a = c.
transitive :: Equal a b -> Equal b c -> Equal a c
transitive EqlZ EqlZ = EqlZ
transitive (EqlS n) (EqlS m) = EqlS (transitive n m)

-- | a + S b = S a + b
succOut :: Natural a -> Natural b -> Equal (a :+: (S b)) (S a :+: b)
succOut NumZ b = reflexivity (NumS b)
succOut (NumS n) m = EqlS $ succOut n m
-- This is the proof that the kata requires.
-- | a + b = b + a
plusCommutes :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
plusCommutes NumZ NumZ = EqlZ
plusCommutes NumZ (NumS n) = EqlS (plusCommutes NumZ n)
plusCommutes (NumS n) NumZ = EqlS (plusCommutes n NumZ)
plusCommutes (NumS n) (NumS m) =  symmetric $ EqlS $ symmetric $ transitive (succOut n m) $ plusCommutes  (NumS n) m

-- | Another type proxy evidence.
times :: Natural a -> Natural b -> Natural (a :*: b)
times NumZ _ = NumZ
times (NumS n) m = plus m (times n m)

-- This will also be helpful
zeroComm :: Natural a -> Equal Z (a :*: Z)
zeroComm NumZ = EqlZ
zeroComm (NumS n) = zeroComm n

leibLPlus :: Natural a -> Natural b -> Natural c -> Equal a b -> Equal (a :+: c) (b :+: c)
leibLPlus _ _ c EqlZ = reflexivity c
leibLPlus (NumS a) (NumS b) c (EqlS eq) = EqlS $ leibLPlus a b c eq

leibRPlus :: Natural a -> Natural b -> Natural c -> Equal a b -> Equal (c :+: a) (c :+: b)
leibRPlus _ _ NumZ eq = eq
leibRPlus a b (NumS c) eq = EqlS $ leibRPlus a b c eq

-- This is the proof that the kata requires.
-- | a * b = b * a
timesComm :: Natural a -> Natural b -> Equal (a :*: b) (b :*: a)
timesComm NumZ m = zeroComm m
timesComm (NumS n) NumZ = symmetric $ zeroComm n
timesComm (NumS n) (NumS m) =
  EqlS
  $ transitive (plusCommutes m (times n (NumS m)))
  $ transitive (leibLPlus (times n (NumS m)) (times (NumS m) n) m (timesComm n (NumS m)))
  $ transitive (symmetric $ plusAssoc n (times m n) m)
  -- n + ((n1 * n) + n1) vs n + (n1 * (S n))
  $ leibRPlus (plus (times m n) m) (times m (NumS n)) n
  -- (m * n) + m = m + (m * n)
  $ transitive (plusCommutes (times m n) m)
  -- m + (m * n) -> m + (n * m)
  $ transitive (leibRPlus (times m n) (times n m) m (timesComm m n))
  -- m + (n * m) -> (m * S n)
  $ timesComm (NumS n) m
