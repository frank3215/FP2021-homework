module HW17 where

lsp :: (a -> Bool) -> [a] -> [a]
lsp p xs = helper p xs [] [] 0 0
    where
        helper :: (a -> Bool) -> [a] -> [a] -> [a] -> Int -> Int -> [a]
        helper p [] ys ans curlen maxlen = if curlen > maxlen then reverse ys else reverse ans
        helper p (x : xs) ys ans curlen maxlen | p x = helper p xs (x : ys) ans (curlen+1) maxlen
            | otherwise = if curlen > maxlen then helper p xs [] ys 0 curlen else helper p xs [] ans 0 maxlen

inf :: Int
inf = 1000000000000

minimax :: [[Int]] -> Int
minimax xss = helper inf xss
    where
        helper :: Int -> [[Int]] -> Int
        helper answer [] = answer
        helper answer (xs1 : xss) = helper (min answer (helper2 answer (- inf) xs1)) xss
            where
                helper2 :: Int -> Int -> [Int] -> Int
                helper2 answer current [] = min answer current
                helper2 answer current (x : xs) = if current >= answer then answer else helper2 answer (max current x) xs