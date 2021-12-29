module HW4 where

-- Problem #1: 补全下列值的类型签名
val1 :: [Char]
val1 = ['a', 'b', 'c']

val2 :: (Char, Char, Char)
val2 = ('a', 'b', 'c')

val3 :: [(Bool, Char)]
val3 = [(False, '0'), (True, '1')]

val4 :: ([Bool], [Char])
val4 = ([False, True], ['0', '1'])

val5 :: [[a] -> [a]]
val5 = [tail, init, reverse]
-- End Problem #1

-- Problem #2: 补全下列函数的类型签名
second :: [a] -> a
second xs = head (tail xs)

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

pair :: a -> b -> (a, b)
pair x y = (x, y)

double :: Num a => a -> a
double x = x * 2

palindrome :: Eq a => [a] -> Bool
palindrome xs = reverse xs == xs

twice :: (a -> a) -> a -> a
twice f x = f (f x)
-- End Problem #2

-- Problem #3: Int/Integer，show/read
-- Part #1: Int/Integer的区别
{-
    Int和Integer的区别是……

    Prelude> 2^64 :: Int
    0
    Prelude> 2^64 :: Integer
    18446744073709551616
-}
-- End Part #1

-- Part #2: show/read的用法
{-
    Prelude> show 123
    "123"
    Prelude> read "123" :: Int
    123
-}
-- End Part #2
-- End Problem #3

-- Problem #4: Integral/Fractional
-- Part #1: Integra
{-
    Prelude> quot 31 (-2)
    -15
    Prelude> rem 31 (-2)
    1
    Prelude> quotRem 31 (-2)
    (-15,1)
    Prelude> div 31 (-2)
    -16
    Prelude> mod 31 (-2)
    -1
    Prelude> divMod 31 (-2)
    (-16,-1)
    Prelude> toInteger 31
    31
    Prelude> :type toInteger 31
    toInteger 31 :: Integer
-}
-- End Part #1

-- Part #2: Fractional
{-
    Prelude> fromRational 1
    1.0
    Prelude> :type fromRational 1
    fromRational 1 :: Fractional a => a
    Prelude> recip 0.5
    2.0
    Prelude> 1.0 / 0.5
    2.0
-}
-- End Part #2
-- End Problem #3
