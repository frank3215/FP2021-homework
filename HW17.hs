module HW17 where

lsp :: (a -> Bool) -> [a] -> [a]
lsp p xs = helper p xs [] [] 0 0
    where
        helper :: (a -> Bool) -> [a] -> [a] -> [a] -> Int -> Int -> [a]
        helper p [] ys ans curlen maxlen = if curlen > maxlen then reverse ys else reverse ans
        helper p (x : xs) ys ans curlen maxlen | p x = helper p xs (x : ys) ans (curlen+1) maxlen
            | otherwise = if curlen > maxlen then helper p xs [] ys 0 curlen else helper p xs [] ans 0 maxlen

-- 注：因为担心在列表的末尾增加元素是O(列表长度)的，这份代码将列表倒了过来，把从列表尾部加入元素变成了在列表头部加入元素，这样能保证是O(1)的
-- 证明O(n)复杂度：相当于证明操作的复杂度是均摊O(1)的。
--  势能分析：令势能=当前存储的序列ys的长度，则每次操作的代价至多是3：
--  1. 当前存储的序列ys变为(x : ys)：代价为1（势能） + 1（操作）=2。
--  2. 将序列赋值给答案，清空当前序列：用势能（length ys）支付，代价1（操作）。
--  3. 将答案reverse：整个程序仅在终止时操作一遍，复杂度O(n)
--  因此，总复杂度是O(n)的。


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
