{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language FunctionalDependencies #-}
{-# Language GADTs #-}

module PolyFuns where

----------------------------------------
  -- Poly Add
----------------------------------------

-- | Main class 'Base'.
class Base a r | r -> a where
  base :: r -- ^ No argument
  sapp :: a -> r -- ^ At least one argument

-- | Base for Int, zero and just identity.
instance Base Int Int where
  base = 0
  sapp = id

-- | Recursive call generation base on result type form.
-- For each '->' found in the result type, this instance generates a recursive
-- call for another Base (minus one '->')
instance (a ~ Int, Base a r) => Base a (a -> r) where
  base = sapp
  sapp a b = sapp (a + b)

polyAdd :: (a ~ Int, Base a r) => r
polyAdd = base

----------------------------------------
  -- Poly List
----------------------------------------

class PList a r | r -> a where
   zeroL :: r
   plist :: [a] -> a -> r

instance PList a [a] where
  zeroL = []
  plist xs x = reverse $ x : xs

-- | Pretty much the same as Base
instance PList a r => PList a (a -> r) where
  zeroL = plist []
  plist xs x y = plist (x:xs) y

-- `polyList` turns its arguments into a list, polymorphically.
polyList :: PList a r => r
polyList = zeroL

----------------------------------------
  -- Poly Words
----------------------------------------
-- -- `polyWords` turns its arguments into a spaced string.
class CString a r | r -> a where
  zeroArgs :: r
  concat'  :: a -> r

instance CString String String where
  zeroArgs = []
  concat'  = id

instance (a ~ String, CString a r) => CString a (a -> r) where
  zeroArgs = concat'
  concat' w1 w2 = concat' (w1 ++ ' ' : w2)

polyWords :: (a ~ [Char], CString a r) => r
polyWords = zeroArgs
