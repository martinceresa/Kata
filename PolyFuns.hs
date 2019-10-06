{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language FlexibleContexts #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language FunctionalDependencies #-}
{-# Language GADTs #-}
module PolyFuns where

-- The thing is I need to make some recursive definitions...

-- type family Polyfun a b where
--   Polyfun a a = a
--   Polyfun (a -> a) a =

class PVar a r | r -> a where
  app :: a -> a -> r

instance PVar Int Int where
  app = (+)

instance PVar a a => PVar a (a -> a) where
  app a b c = app (app a b) c

class PInt r where
  appP :: Int -> Int -> r

instance PInt Int where
  appP = (+)

instance (PInt r) => PInt (Int -> r) where
  appP a b z = appP (appP a b) z

addP :: PVar Int r => Int -> r
addP = app 0

-- test :: Int
-- test = polyAdd (1 :: Int) (2 :: Int) (3 :: Int)


-- -- `polyList` turns its arguments into a list, polymorphically.
-- polyList :: ???
-- polyList = error "TODO: polyList"

-- -- `polyWords` turns its arguments into a spaced string.
-- polyWords :: ???
-- polyWords = error "TODO: polyList"
