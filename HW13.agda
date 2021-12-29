module HW13 where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

module problem-1 where

  _<_ : Nat -> Nat -> Bool
  _ < zero = false
  zero < _ = true
  suc x < suc y = x < y

module problem-2 where

  filter : {A : Set} -> (A -> Bool) -> (List A) -> (List A)
  filter p [] = []
  filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  --infixl 80 _::_
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vec (Vec A n) m

vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

vec : {n : Nat}{A : Set} -> A -> Vec A n
vec {zero} x = []
vec {suc n} x = x :: vec {n} x

infixl 90 _$_
_$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
[] $ [] = []
(f :: fs) $ (x :: xs) = f x :: fs $ xs

transpose : {A : Set}{n m : Nat} -> Matrix A n m -> Matrix A m n
transpose {n = n}{m = zero} [] = vec []
transpose {n = n}{m = suc m} (xs :: xss) = ( (vec (\x -> \xs -> x :: xs)) $ xs ) $ transpose xss
{-
head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

id : {A : Set} -> A -> A
id x = x

_o_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set} (f : {x : A}(y : B x) -> C x y) (g : (x : A) -> B x) (x : A) -> C x (g x)
(f o g) x = f (g x)
-}