{-# LANGUAGE TemplateHaskell #-}
module Kata.TupleMaker (tuple) where

import Language.Haskell.TH

{-
Url: https://www.codewars.com/kata/59c6fa2886a6fd5f820000b4
Description:
The Task
Your task is to use Template Haskell to create a simple metafunction called
tuple :: Int -> Q Exp.

This is how it will behave:

λ> $(tuple 2) 1 "Hello"
(1,"Hello")
λ> $(tuple 5) 5 4 3 2 1
(5,4,3,2,1)
λ> $(tuple 3) True 'λ' GT
(True, 'λ', GT)
In other words, it creates a function, which in turn takes n arguments, and
wraps them all into a tuple.

There are two edge cases that you must be aware of:

λ> $(tuple 0)
()
λ> $(tuple 1) "Hello!"
"Hello!"
λ> $(tuple 1) 132
132
In other words, tuple 0 produces (), and tuple 1 produces the identity function.

Possible Hurdles Most of the challenge here is in getting the program to
actually type check. Hence, most test failures will be due to compilation
errors.

Many of the tests created here are generated automatically metaprogramatically,
so some of the errors may be somewhat strange to read. However, GHC often has
very readable errors when it comes to Template Haskell.
-}

-- | Creates a lambda that takes `n` arguments and
-- | returns an n-tuple of those arguments.
tuple :: Int -> Q Exp
tuple n =
         let names = zipWith (\x i -> mkName (x ++ show i)) (replicate n "x") ([0 .. ] :: [Int])
         in lamE ( map varP names)
            (tupE $ map varE names)
