module MiniStringFuck where

data Mem =  M { cell :: Int, out :: String}
  deriving Show

tick :: Mem -> Mem
tick (M m o) = M (mod (succ m) 256) o

oput :: Mem -> Mem
oput (M c o) = M c (toEnum c : o)

interpret :: Char -> Mem -> Mem
interpret c | c == '+' = tick
            | c == '-' = oput
            | otherwise = id

step :: String -> Mem -> Mem
step [] m = m
step (c:cs) m = step cs (interpret c m)

myFirstInterpreter :: String -> String
myFirstInterpreter = reverse . out . flip step (M 0 "")
