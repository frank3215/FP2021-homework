module HW5 where

import Data.Char

-- Problem #1: define safetail
-- Part #1: use a conditional expression
safetail1 :: [a] -> [a]
safetail1 x = if null x then [] else tail x
-- End Part #1

-- Part #2: use guarded equations
safetail2 :: [a] -> [a]
safetail2 x | null x    = []
            | otherwise = tail x
-- End Part #2

-- Part #3: use pattern matching
safetail3 :: [a] -> [a]
safetail3 [] = []
safetail3 xs = tail xs
-- End Part #3
-- End Problem #1

-- Problem #2: Luhn algorithm
luhn_double :: Int -> Int
luhn_double x = if 2*x > 9 then 2*x-9 else 2*x

luhn :: Int -> Int -> Int -> Int -> Bool
luhn a b c d = (luhn_double a + b + luhn_double c + d) `mod` 10 == 0
-- End Problem #2

-- Problem #3: Caesar crack
table :: [Float]
table = [8.1, 1.5, 2.8, 4.2, 12.7, 2.2, 2.0, 6.1, 7.0, 0.2, 0.8, 4.0, 2.4, 6.7, 7.5, 1.9, 0.1, 6.0, 6.3, 9.0, 2.8, 1.0, 2.4, 0.2, 2.0, 0.1]

let2int :: Char -> Int
let2int c = ord c - ord 'a'

int2let :: Int -> Char
int2let n = chr (ord 'a' + n)

shift :: Int -> Char -> Char
shift n c | isLower c = int2let ((let2int c + n) `mod` 26)
          | otherwise = c

encode :: Int -> String -> String
encode n xs = [shift n x | x <- xs]

percent :: Int -> Int -> Float
percent n m = (fromIntegral n / fromIntegral m) * 100

position :: Eq a => a -> [a] -> Int
position x xs = head [i | (x',i) <- zip xs [0..], x == x']

rotate :: Int -> [a] -> [a]
rotate n xs = drop n xs ++ take n xs

crack :: String -> String
crack xs = encode (-factor) xs
  where factor = position (minimum chitab) chitab
        chitab = [chisqr (rotate n table') table | n <- [0..25]]
        table' = freqs xs
        freqs xs = [ fromIntegral (length [ x | x <- xs, x == n ]) / fromIntegral (length [x | x <- xs, 'a' <= x && x <= 'z']) * 100 | n <- ['a'..'z']]
        chisqr os es = sum [ (o-e)^2/e | (o,e) <- zip os es]
-- End Problem #3

-- Problem #4: Pythagorean triples
pyths :: Int -> [(Int, Int, Int)]
pyths n = [(x,y,z) | x <- [1..n], y <- [1..n], z <- [1..n], x^2 + y^2 == z^2]
-- End Problem #4

-- Problem #5: perfect integers
factors :: Int -> [Int]
factors n = [x | x <- [1..n], n `mod` x == 0]

perfects :: Int -> [Int]
perfects n = [x | x <- [1..n], sum (factors x) == 2*x]
-- End Problem #5

-- Problem #6: scalar product
scalarProduct :: Num a => [a] -> [a] -> a
scalarProduct xs ys = sum [x*y | (x,y) <- zip xs ys]
-- End Problem #6
