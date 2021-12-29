module HW10 where

import Control.Monad (ap)
import Control.Applicative
import Data.Char
import GHC.ResponseFile (expandResponse)

-- Problem #1: Reader Monad
-- 因为 ((->) a) 在标准库中已经实现了 Monad，所以我们使用下面这个新定义的类型代替
newtype Reader r a = Reader { runReader :: r -> a }

instance Functor (Reader r) where
  -- fmap :: (a -> b) -> ((Reader r) a) -> ((Reader r) b)
  -- f :: a -> b
  -- g :: r -> a
  -- aim: r -> b
  fmap f (Reader g) = Reader (f . g)

instance Applicative (Reader r) where
  -- pure :: a -> ((Reader r) a)
  -- 懒得验证是不是满足那些laws了……下同
  pure a = Reader (const a)
  -- (<*>) :: ((Reader r) (a->b)) -> ((Reader r) a) -> ((Reader r) b)
  (<*>) (Reader f) (Reader x) = Reader (\r -> f r (x r))

instance Monad (Reader r) where
  -- (>>=) :: ((Reader r) a) -> (a -> (Reader r) b) -> ((Reader r) b)
  (>>=) (Reader r2a) a2Rrb = Reader (\r -> runReader (a2Rrb (r2a r)) r)
-- End Problem #1

-- Problem #2: Functor, Applicative, Monad
data Expr a
  = Var a
  | Val Int
  | Add (Expr a) (Expr a)
  deriving (Show)

instance Functor Expr where
  -- fmap :: (a -> b) -> (Expr a) -> (Expr b)
  fmap f (Var a) = Var (f a)
  fmap f (Val a) = Val a
  fmap f (Add a b) = Add (fmap f a) (fmap f b)

instance Applicative Expr where
  pure = Var
  (<*>) (Val a) _ = Val a
  (<*>) (Var a) b = fmap a b
  (<*>) (Add a b) x = Add (a <*> x) (b <*> x)
  -- (<*>) = ap


instance Monad Expr where
  -- (>>=) :: m a -> (a -> m b) -> m b
  (>>=) (Var a) f = f a
  (>>=) (Val a) f = Val a
  (>>=) (Add a b) f = Add (a >>= f) (b >>= f)
-- End Problem #2

-- Problem #3: Why does factorising the expression grammar make the resulting parser more efficient?
-- 因为 (term '+' expr | term) 不 factorise 的话 term 就会执行2次，效率较低。
-- 如果 factorise 成 (term ('+' expr | e)) 的话，term只会运行一次，效率较高。
-- End Problem #3

-- Problem #4: Extend the expression parser
newtype Parser a = P { parse :: String -> [(a,String)] }

instance Functor Parser where
  fmap f p = P(\xs -> case parse p xs of
    [] -> []
    [(a,xs')] -> [(f a, xs')]
    )

instance Applicative Parser where
  pure a = P(\xs -> [(a,xs)])
  (<*>) px py = P(\xs -> case parse px xs of
    [] -> []
    [(f,xs')] -> parse (fmap f py) xs'
    )

instance Monad Parser where
  (>>=) p f = P (\xs -> case parse p xs of
    [] -> []
    [(x,xs')] -> parse (f x) xs'
    )

instance Alternative Parser where
  empty = P (const [])
  (<|>) px py = P (\xs -> case parse px xs of
      [] -> parse py xs
      [(a,xs')] -> [(a,xs')]
    )

item :: Parser Char
item = P (\xs -> case xs of
  [] -> []
  (x:xs) -> [(x, xs)]
  )

sat :: (Char -> Bool) -> Parser Char
sat p = do
  x <- item
  if p x then return x else empty

digit :: Parser Char
digit = sat isDigit

char :: Char -> Parser Char
char c = sat (== c)

nat :: Parser Int
nat = do
  x <- some digit
  return (read x)

int :: Parser Int
int = do
  char '-'
  x <- nat
  return (-x)
 <|> nat

factor :: Parser Int
factor = nat <|> do
  char '('
  x <- expr
  char ')'
  return x

{-
term :: Parser Int
term = do {
  x <- factor;
  do {
    char '*';
    term
  } <|> do {
    char '/';
    term
  } <|> return x
}
-}

term' :: Parser ((Int->Int)->Int)
term' = do
  x <- factor
  do
    char '*'
    y <- term'
    return (\f -> y ((f x)*))
   <|> do
    char '/'
    y <- term'
    return (\f -> y ((f x)`div`))
   <|> return (\f -> f x)

expr' :: Parser ((Int->Int)->Int)
expr' = do
  x' <- term'
  let x = x' id
  do
    char '+'
    y <- expr'
    return (\f -> y ((f x)+))
   <|> do
    char '-'
    y <- expr'
    return (\f -> y ((f x)-))
   <|> return (\f -> (f x))

expr :: Parser Int
expr = do
  f <- expr'
  return (f id)

eval :: String -> Int
eval = fst . head . parse expr
-- End Problem #4