{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase    #-}
module Coroutine where

import           Control.Monad (ap, forever)

newtype Coroutine r u d a
  = Coroutine { runCoroutine :: (Command r u d a -> r) -> r }
  deriving (Functor)

data Command r u d a
  = Done a
  | Out d (Coroutine r u d a)
  | In (u -> Coroutine r u d a) deriving Functor

-- Useful alias
apply :: Coroutine r u d a -> (Command r u d a -> r) -> r
apply = runCoroutine

(!) ::  (Command r u d a -> r) -> Coroutine r u d a -> r
(!) = flip apply

instance Applicative (Coroutine r u d) where
  pure = return
  (<*>) = ap

instance Monad (Coroutine r u d) where
  -- Nothing to do, just continue with x
  return x = Coroutine ($(Done x))
  -- Given f :: Coroutine r u d a
  -- and   g :: a -> Coroutine r u d b
  -- form a Coroutine r u d b.
  f >>= g = Coroutine $ \k -> apply f (\case
                              -- | f is just a value a
                              Done a -> apply (g a) k
                              -- | f gives a value back, so I just throw it to k
                              -- and continue binding.
                              Out d f' -> k $ Out d (f' >>= g)
                              -- | f expects a value, so we basically delay
                              -- binding with g until a value is given.
                              In f' -> k (In $ (>>=g) . f'))

{-
The semantics of x >>> y are as follows:
We start by executing y normally until y requests additional input (by the In
constructor). At this point we transfer control to x which executes normally
until it attempts to output (by the Out constructor) at which point we resume
computation of y; the value that x produced in its output is used as y's input.
If either x or y terminate with the value v then v is the value of the whole
pipe.
-}
(>>>) :: Coroutine r u m a -> Coroutine r m d a -> Coroutine r u d a
x >>> y = Coroutine $ \k -> apply y (\case
                                        Done v -> k (Done v)
                                        Out d y' -> k (Out d (x >>> y'))
                                        In y' -> apply (pipe2 x y') k
                                    )

-- It might be useful to define the following function
pipe2 :: Coroutine r u m a -> (m -> Coroutine r m d a) -> Coroutine r u d a
pipe2 x y = Coroutine
            $ \k -> apply x (\case
                   Done v -> k (Done v)
                   Out d x' -> apply (x' >>> y d) k
                   In x' -> k (In $ flip pipe2 y . x')
                            )
-- Library functions

-- | Oblivious Repeat routine for ever
repeatC :: Coroutine r a v () -> Coroutine r a v ()
repeatC t = t >> repeatC t

-- | nop : No Op
nop :: Coroutine r a v ()
nop = return ()

-- | output: Immediately output the argument.
output :: a -> Coroutine r u a ()
output v = Coroutine $ \k -> k (Out v nop)

-- | input: Waits for an input before returning it.
input :: Coroutine r v d v
input = Coroutine $ \k -> k (In return)

-- | id : Take and return
idC :: Coroutine r v v ()
idC = input >>= output

-- | produce: Output each element in a list in order.
produce :: [a] -> Coroutine r u a ()
produce = foldr (\a r -> output a >> r ) nop

-- | consume: Collect all outputted values into a list.
consume :: Coroutine [t] u t a -> [t]
consume ts = apply ts
          (\case
              Done _ -> []
              Out t x -> t : consume x
              In x -> consume $ pipe2 input x
          )

-- | filter: Repeatedly request for input and output it, if it matches a predicate.
filterC' :: (v -> Bool) -> Coroutine r v v ()
filterC' p = input >>= \v -> if p v then output v else nop

filterC :: (v -> Bool) -> Coroutine r v v ()
filterC = repeatC . filterC'

-- | limit: Allow n items to pass through before terminating (similar to take from the prelude).
limit :: Int -> Coroutine r v v ()
limit n | n <= 0 = nop
        | otherwise = idC >> limit (n-1)

-- | suppress: Disallow the first n items to pass through (similar to drop from the prelude).
suppress :: Int -> Coroutine r v v ()
suppress n | n <= 0 = repeatC idC
           | otherwise = input >> suppress (n-1)

-- | add: Repeatedly take two inputs and output their sum.
add' :: Coroutine r Int Int ()
add' = do
  n <- input
  m <- input
  output (n + m)

add :: Coroutine r Int Int ()
add = repeatC add'

appe :: (a -> b) -> Coroutine r a b ()
appe f = input >>= output . f

suc :: Coroutine r Int Int ()
suc = appe succ

-- | duplicate: Repeatedly receive input and output it twice.
duplicate' :: Coroutine r v v ()
duplicate' = input >>= \v -> output v >> output v

duplicate :: Coroutine r v v ()
duplicate = repeatC duplicate'

-- Notice that add and duplicate should never terminate.
scanlC' :: (b -> a -> b) -> b -> Coroutine r a b ()
scanlC' f q = output q >> input >>=  output . f q -- return . f q

scanlC :: (b -> a -> b) -> b -> Coroutine r a b ()
scanlC f q = repeatC (scanlC' f q)

-- Programs
-- 1. A program which outputs the first 5 even numbers of a stream.
-- 2. A program which produces a stream of the triangle numbers
-- 3. A program which multiplies a stream by 2
-- 4. A program which sums adjacent pairs of integers

p1, p2, p3, p4 :: Coroutine r Int Int ()

p1 = filterC even >>> limit 5
p2'' j m = output m >> p2'' (j + 1) (j + m + 1)
p2 = p2'' 1 1
p3 = duplicate >>> add
-- Better solution, after submission
p4 = duplicate >>> suppress 1 >>> add

-- || My solution
-- p1 = filterC even >>> limit 5
-- p2'' j m = output m >> p2'' (j + 1) (j + m + 1)
-- p2 = p2'' 1 1
-- p3 = duplicate >>> add
-- p4' n = do
--   m <- input
--   output (n + m)
--   p4' m
-- p4 = input >>= p4'
