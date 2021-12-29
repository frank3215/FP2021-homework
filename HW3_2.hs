-- 猜数字小游戏
module Main where
import Prelude
-- import System.Random (RandomRIO)

guess :: Integer -> IO()

guess answer = do
    putStrLn "Your Guess:"
    attempt <- getLine
    let n = (read attempt :: Integer)
    if n == answer then putStrLn "ACcpeted!" else if n > answer then do
        putStrLn "Wrong Answer! (Too Large)"
        guess answer
    else do
        putStrLn "Wrong Answer! (Too Small)"
        guess answer

main :: IO ()
main = do
    x <- RandomRIO(1,100)
    guess 1
