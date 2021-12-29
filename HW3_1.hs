module HW3_1 where

-- Problem #1: 写出 and 函数的三种其他的定义
and1 :: Bool -> Bool -> Bool
and1 x y | x         = y
         | otherwise = False

and2 :: Bool -> Bool -> Bool
and2 x y = if x == True then y else False

and3 :: Bool -> Bool -> Bool
and3 x y = not (or(not x, not y))
-- End Problem #1

-- Problem #2: 给出函数 div 的一种或多种定义
div1 :: Integer -> Integer -> Integer
div1 x y | y > 0 && x >= y    = 1 + div1 (x-y) y
         | y > 0 && x < 0     = (-1) + div1 (x+y) y
         | y > 0              = 0
         | y < 0 && x <= y    = 1 + div1 (x-y) y
         | y < 0 && x > 0     = (-1) + div1 (x+y) y
         | y < 0              = 0
-- End Problem #2

-- Problem #3: 写出阶乘函数的其他定义：
-- Part #1: 使用条件方程组
factGuard :: Integer -> Integer
factGuard x | x == 0    = 1
            | x > 0     = x*(factGuard(x-1))
-- End Part #1

-- Part #2: 使用分支表达式
factBranch :: Integer -> Integer
factBranch x = if x == 0 then 1 else x*(factBranch(x-1))
-- End Part #2
-- End Problem #3
