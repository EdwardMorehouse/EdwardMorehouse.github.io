{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 5, 2023-02-27
 -- 
 -- Programming Interfaces
 --}

module Lecture5

import Data.List


{-
  Last time: Higher-order functions and function literals.
-}

-- Recall the definition for the type Bool:
data Bool' : Type where
  True' : Bool'
  False' : Bool'

-- fold_bool:
fold_bool : (tt: t) -> (ff : t) -> Bool -> t
fold_bool tt ff False = ff
fold_bool tt ff True = tt

{-
  Today's lecture
  ---------------
  Interfaces - give specific behaviour to generic types (similar to 
  typeclasses or abstract classes in other languages).
  
  These allow us to constrain generic functions, and provide a kind of
  'ad-hoc polymorphism' or 'overloading' of functions.
  
  We will see some interfaces from the standard library and learn how 
  to write implementations for these interfaces. Then, we will learn 
  how to define our own interfaces.
  
  In this lecture we focus on interfaces parameterized by basic types.
  In week 8 we will see more interfaces with 'higher-order' parameters.
-}

-- Defining add as a "generic" function:
add : Num a => a -> a -> a
add x y = x + y


-- The Num interface:
-- interface Num ty where
--   (+) : ty -> ty -> ty
--   (*) : ty -> ty -> ty 
--   fromInteger : Integer -> ty


implementation Num Bool where
  (+) x y = (x && not y) || (not x && y)
  (*) x y = x && y
  fromInteger x = True

{- Show: an interface for string representations of types -}

interface Show' ty where
  show' : ty -> String

implementation Show' Bool where
  show' False = "False"
  show' True = "True"



-- Named implementations

implementation [ind] Show Nat where
  show Z = "Z"
  show (S k) = "S(" ++ show k ++ ")"


-- Syntax: show @{ind} 0

-- Multiple constraints
implementation [Lecture5] Show a => Show b => Show (Pair a b) where
  show (x, y) = "(" ++ show x ++ "," ++ show y ++ ")"
  
-- show @{Lecture5} (3, True)

implementation [Lecture5inv] Show a => Show b => Show (Pair a b) where
  show (x, y) = "(" ++ show y ++ "," ++ show x ++ ")"
  

{- Eq: an interface for equality/inequality -}

-- interface Eq ty where
--   (==) : ty -> ty -> Bool
--   (/=) : ty -> ty -> Bool
-- --The following allow for default implementations;
-- --We can overwrite the behaviour for a default implementation.
--   x == y = not (x /= y)
--   x /= y = not (x == y)

occurrences : Eq a => (item : a) -> (l : List a) -> Nat
occurrences item [] = 0
occurrences item (x :: xs) = case x == item of
  False => occurrences item xs
  True => 1 + occurrences item xs

-- Test on: occurrences "a" ["a", "b", "a"]


-- A type of arithmetic expressions:
data AExpr : Type -> Type where
  V : n -> AExpr n
  Plus : AExpr n-> AExpr n-> AExpr n
  Times : AExpr n -> AExpr n -> AExpr n


eval : Num n => AExpr n -> n
eval (V x) = x
eval (Plus x y) = eval x + eval y
eval (Times x y) = eval x * eval y

-- Test on: eval (Plus (V 1) (V 2))

implementation Num n => Eq n => Eq (AExpr n) where
  (==) x y = eval x == eval y


-- Test on: Plus (V 1) (V 2) == (Plus (V 1) (V 2)) 

data Tree : Type -> Type where
  Leaf : Tree a
  Branch : (left : Tree a) -> (val : a) -> (right : Tree a) -> Tree a


-- Equality for trees
implementation Eq a => Eq (Tree a) where
  (==) Leaf Leaf = True
  (==) (Branch l v r) (Branch x y z) = l == x && v == y && r == z
  (==) _ _ = False

-- Test on: (Branch Leaf 4 (Branch Leaf 1 Leaf)) == (Branch Leaf 4 (Branch Leaf 1 Leaf))


{- Ord : an interface for comparing values of orderable types -}

-- interface Eq a => Ord' a where
--   compare : ty -> ty -> Ordering
--   (<) : a -> a -> Bool
--   (>) : a -> a -> Bool
--   (<=) : a -> a -> Bool
--   (>=) : a -> a -> Bool
--   max : a -> a -> a
--   min : a -> a -> a


quicksort : Ord a => List a -> List a
quicksort [] = []
quicksort (x :: xs) = 
  let lower = filter (< x) xs
      upper = filter (>= x) xs in
  (quicksort lower) ++ [x] ++ (quicksort upper)


-- 
data Animal : Type where
  Insect : Animal
  Mouse : Animal
  Owl : Animal

-- To implement the Ord interface, we need to implement Eq.
implementation Eq Animal where
  (==) Insect Insect = True
  (==) Mouse Mouse = True
  (==) Owl Owl = True
  (==) _ _ = False

-- "Food Chain"
implementation Ord Animal where
  (<) Insect Mouse = True
  (<) Insect Owl = True
  (<) Mouse Owl = True
  (<) _ _ = False

 
{- Cast: an interface for casting types -}

interface Cast' from to where
  cast' : from -> to


Num n => Cast (AExpr n) n where
  cast e = eval e
 
--Test on: the Integer (cast (Plus (V 1) (V 2)))

