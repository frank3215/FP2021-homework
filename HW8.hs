module HW8 where

import Data.List

-- 为简便起见，我们不允许任何中间结果超出 2^32。
-- 这意味着可以提前对搜索进行剪枝：
-- 1. 任何结果均不允许超过 2^32。
-- 2. 任何指数均不允许超过 32。
-- 在大家的 64 位系统上，GHC 一般把 Int 实现为 64 位整数，因此
-- 只要严格执行上述剪枝策略，就不必担心运算溢出问题。

type I = Int

data Op
  = Add
  | Sub
  | Mul
  | Div
  | Exp
  -- 提示：添加指数运算
  deriving Eq

ops :: [Op]
ops = [Add,Sub,Mul,Div,Exp]

apply :: Op -> Int -> Int -> Int
apply Add x y = x + y
apply Sub x y = x - y
apply Mul x y = x * y
apply Div x y = x `div` y
apply Exp x y = x ^ y

valid :: Op -> Int -> Int -> Bool
valid Add x y = x <= y && x + y < 2^32
valid Sub x y = x > y && x * y < 2^32
valid Mul x y = x /= 1 && y /= 1 && x <= y
valid Div x y = y /= 1 && x `mod` y == 0
valid Exp x y = x /= 1 && y /= 1 && fromIntegral(y) * log(fromIntegral(x)) < 32*log(2)

data Expr
  = Val I
  | App Op Expr Expr
  deriving Eq

type An = (I, Expr)
type Ans = [(I, Expr)]

-- 你需要完成下面的 solutions 函数

solutions :: [I] -> I -> [Expr]
solutions xs n = [e | (x, e) <- res, abs(x-n) == ep]
    where
      res = result xs
      ep = foldr min (2^32) ([abs(x-n) | (x,e) <- res])

{-
solutions :: [I] -> I -> [Expr]
solutions xs n = [e | (x, e) <- res, x == n']
    where
        res = solutions' xs n
        n' = fst (head (sort' res))
-}

{-
solutions' :: [I] -> I -> Ans
solutions' xs n = [(abs(x-n),e) | (x,e) <- result xs]

sort' :: Ans -> Ans
sort' = sortBy cmp

cmp :: An -> An -> Ordering
cmp xe ye
  | x < y  = LT
  | x == y = EQ 
  | x > y  = GT
  where
    (x,_) = xe
    (y,_) = ye
-}


result :: [I] -> Ans
result xs = concat [results' xs' | xs' <- allSubsets xs]

allSubsets :: [a] -> [[a]]
allSubsets [] = []
allSubsets [x] = [[x]]
allSubsets (x:xs) = (map (x:) as) ++ as
  where
    as = allSubsets xs

results' :: [I] -> Ans
results' [] = []
results' xs | length xs == 1 = [(x, Val x) | x <- xs]
            | otherwise = concat [combine ya za | (ys, zs) <- splits xs, ya <- results' ys, za <- results' zs]

-- concat [combine ya za | (ys, zs) <- [([3],[7,50,10,25])], ya <- results' ys, za <- results' zs]

combines :: Ans -> Ans -> Ans
combines xs ys = concat [ combine x y | x <- xs, y <- ys]

combine :: An -> An -> Ans
combine xe ye = [(apply z x y, App z ex ey) | z <- ops, valid z x y]
  where
    (x,ex) = xe
    (y,ey) = ye

splits :: [I] -> [([I],[I])]
splits [] = []
splits [_] = []
splits (x:xs) = ([x], xs):(xs, [x]):(map tofst res ++ map tosnd res)
  where
    res = splits xs
    tofst (ys, zs) = (x:ys, zs)
    tosnd (ys, zs) = (ys, x:zs)

-- 下面是我们为 Expr 和 Op 提供的一个 Show 的实现
-- 这并不是本次作业必需的，但是在调试过程中可能会让表达式更易读
-- 这个实现使用了 showsPrec，有关它的细节你可以参考相关文档：
-- https://hackage.haskell.org/package/base-4.15.0.0/docs/Text-Show.html#t:Show
-- 以及 Haskell 2010 Report 的 11.4 节：
-- https://www.haskell.org/onlinereport/haskell2010/haskellch11.html

instance Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Exp = "^"
  -- 提示：指数运算可以显示为 x ^ y

instance Show Expr where
  showsPrec _ (Val n) = shows n
  showsPrec p (App op x y)
    = showParen (p > q)
    $ showsPrec q x . showChar ' ' . shows op
    . showChar ' ' . showsPrec (succ q) y
    where q = case op of
            Add -> 6; Sub -> 6
            Mul -> 7; Div -> 7
            Exp -> 8
            -- 提示：给出指数运算的优先级
            -- 可以参考Haskell定义的优先级（:info ^）

main :: IO ()
main = do
  print (head (solutions [2,2,2,2] 1000))