{-# LANGUAGE TypeOperators, TypeFamilies, GADTs #-}

module Kata.AdditionAssoc where

{- Kata: https://www.codewars.com/kata/a-plus-b-plus-c-equals-a-plus-b-plus-c-prove-it/train/haskell
Inspired from the a+b=b+a kata, and this one is much simpler.

The definition of natural numbers are all the same, the only difference is the theorem to be proved. This time we're gonna prove the plus associative law.
  -}
-- import Kata.AdditionAssoc.Definitions

{- Preloaded code, might be helpful for
   doing this Kata locally
  -}

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

-- Helpers

-- | For any n, n = n.
reflexive :: Natural n -> Equal n n
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS (reflexive n)

-- | if a = b, then b = a.
symmetric :: Equal a b -> Equal b a
symmetric EqlZ = EqlZ
symmetric (EqlS n) = EqlS (symmetric n)

-- | Plus definition. It helps as evidence for reflexivity.
plus :: Natural a -> Natural b -> Natural (a :+: b)
plus NumZ b = b
plus (NumS a) b = NumS $ plus a b

-- This is the proof that the kata requires.
-- | a + (b + c) = (a + b) + c
plusAssoc :: Natural a -> Natural b -> Natural c -> Equal (a :+: (b :+: c)) ((a :+: b) :+: c)
plusAssoc NumZ a b = reflexive $ plus a b
plusAssoc (NumS n) a b = EqlS $ plusAssoc n a b
