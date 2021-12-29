module HW12 where

-- Problem #1: maximum segment sum, the straightforward version
segs :: (Num a, Ord a) => [a] -> [[a]]
segs xs = let n = length xs in [drop (l-1) . take r $ xs | l <- [1..n], r <- [1..n], l <= r]

sums :: (Num a) => [[a]] -> [a]
sums = map sum

max' :: (Ord a, Num a) => [a] -> a
max' = foldr max 0

mss :: (Num a, Ord a) => [a] -> a
mss = max' . sums . segs
-- End Problem #1

-- Problem #2: maximum segment sum, the smart solution
mssSmart :: (Num a, Ord a) => [a] -> a
mssSmart xs = solve 0 xs
    where
        solve s [] = max s 0
        solve s (x:xs) = max s . solve (max 0 (s+x)) $ xs
-- End Problem #2

{-
gen 0 = [[]]
gen n = [ x:xs | x <- [-1..1], xs <- gen (n-1)]

check n = and [ mss xs == mssSmart xs | xs <- gen n]
-}