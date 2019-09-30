module Faberge where

import Data.Array
import Control.Monad.State

type Matrix a = Array (Integer,Integer) a
-- type St = State (Matrix (Maybe Integer))

access :: Integer -> Integer -> Matrix a ->  a
access i j m = m ! (i,j)

update :: Integer -> Integer -> Integer -> Matrix (Maybe Integer) -> Matrix (Maybe Integer)
update i j n m = m//[((i,j),Just n)]

height' :: Integer -> Integer -> Matrix (Maybe Integer) -> (Matrix (Maybe Integer), Integer)
height' n m subCases = 
          maybe 
            (
            let (c , nmp) = height' n (m-1) subCases
                (c', npm) = height' (n-1) (m-1) c
                res = nmp + npm + 1
            in (update n m res c' , res)
            )
            (\i -> (subCases, i))
            $ access n m subCases

heigth :: Integer -> Integer -> Integer 
heigth n m = snd $ height' n m $ array ((0,0),(n+1,m+1))
                  ( 
                  [ ((0,i), Just 0) | i <- [0 .. m]]
                  ++ [ ((i,0), Just 0) | i <- [0 .. n]]
                  ++ [ ((1,i), Just i) | i <- [1 .. m]]
                  ++ [ ((i,1), Just 1) | i <- [1 .. n]]
                  ++ [((i,j), Nothing) | i <- [2..n], j <- [2..m]] )
