module HW7 where

-- Problem #1: multiplies for natural numbers
data Nat = Zero | Succ Nat
  deriving (Show)

add :: Nat -> Nat -> Nat
add Zero     n = n
add (Succ m) n = Succ (add m n)

multiplies :: Nat -> Nat -> Nat
multiplies Zero n = Zero
multiplies (Succ m) n = add (multiplies m n) n
-- End Problem #1

-- Problem #2: folde for Exprs
data Expr
  = Val Int
  | Add Expr Expr
  | Mul Expr Expr
  deriving (Show)

-- try to figure out the suitable type yourself
folde :: (Int -> a) -> (a -> a -> a) -> (a -> a -> a) -> Expr -> a
folde f g h (Val a) = f a
folde f g h (Add a b) = g (folde f g h a) (folde f g h b)
folde f g h (Mul a b) = h (folde f g h a) (folde f g h b)
{-
    *HW7> eval = folde id (+) (*)
    *HW7> eval (Val 1)
    1
    *HW7> eval (Add (Val 1) (Val 2))
    3
-}
-- End Problem #2

-- Problem #3: recursive tree type
data Tree a = Leaf a | Node (Tree a) (Tree a)
-- End Problem #3
