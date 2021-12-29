module Main where

getInt :: IO Int
getInt = do
    line <- getLine
    return (read line :: Int)


adder :: IO Int
adder = adder' 5

adder' :: Int -> IO Int
adder' 0 = do
    return 0
adder' n = do
    x <- getInt
    y <- adder' (n-1)
    return (x+y)

main :: IO ()
main = do
    x <- adder
    print(x)