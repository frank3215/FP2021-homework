module HW11 where

import Prelude hiding (Maybe(..))

-- Problem #1: Maybe, Foldable and Traversable
data Maybe a = Nothing | Just a
  deriving (Show, Eq, Ord)

instance Functor Maybe where
  fmap f Nothing = Nothing
  fmap f (Just a) = Just (f a)

instance Foldable Maybe where
  foldMap f Nothing = mempty
  foldMap f (Just a) = f a
  foldr f v Nothing = v
  foldr f v (Just a) = f a v
  foldl f v Nothing = v
  foldl f v (Just a) = f v a

foldMaybe :: Monoid a => Maybe a -> a
foldMaybe Nothing = mempty
foldMaybe (Just a) = a

instance Traversable Maybe where
  -- traverse :: (a -> f b) -> Maybe a -> f (Maybe b)
  traverse f Nothing = pure Nothing
  traverse f (Just a) = Just <$> f a
-- End Problem #1

-- Problem #2: Tree, Foldable and Traversable
data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving Show

instance Functor Tree where
  fmap f Leaf = Leaf
  fmap f (Node l a r) = Node (fmap f l) (f a) (fmap f r)

instance Foldable Tree where
  foldMap f Leaf = mempty
  foldMap f (Node l a r) = foldMap f l <> f a <> foldMap f r
  -- foldr :: (a -> b -> b) -> b -> Tree a -> b
  foldr f v t = foldr f v (foldMap (:[]) t)
  foldl f v t = foldl f v (foldMap (:[]) t)

foldTree :: Monoid a => Tree a -> a
foldTree = foldMap id

instance Traversable Tree where
  -- traverse :: (a -> f b) -> Tree a -> f (Tree b)
  traverse f Leaf = pure Leaf
  traverse f (Node l a r) = Node <$> traverse f l <*> f a <*> traverse f r
-- End Problem #2

-- Problem #3: fibonacci using zip/tail/list-comprehension
fibs :: [Integer]
fibs = 0:1:[ x+y | (x,y) <- zip fibs (tail fibs)]
-- End Problem #3

-- Problem #4: Newton's square root
approx :: Double -> [Double]
approx n = 1.0:[ (x + (n/x))/2 | x <- approx n ]

sqroot :: Double -> Double
sqroot n = head [ x | (x, y) <- zip (approx n) (tail (approx n)), abs(x-y) < eps]
  where
    eps = 0.00001
-- End Problem #4