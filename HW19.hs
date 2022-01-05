module HW19 where

-- BMF3-2
tailsums :: Num a => [a] -> [a]
tailsums xs = reverse ans
    where
        (_, ans) = foldr (\ a (sum, list) -> (a + sum, a + sum : list)) (0, [0]) xs