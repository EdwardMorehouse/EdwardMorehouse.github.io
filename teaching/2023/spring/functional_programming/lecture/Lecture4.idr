{-- 
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- week 4, 2023-02-20
 -- 
 -- Function Literals and Higher-Order Functions
 --}

module Lecture4

{-- Currying --}
-- Start with an example from Lecture 2.

add  :  Nat -> (Nat -> Nat)
add Z n  =  n
add (S m) n  =  S (add m n)

-- '->' is right - associative: add  :  Nat -> (Nat -> Nat). 
-- Informally think of add as a function taking two arguments 
-- in sequence, but really it's a function taking one argument
-- and returning a function.

-- add 3 behaves like the following:

add3 : Nat -> Nat
add3 x = 3 + x

{-- Generic Higher-Order Functions --}

-- The idea of functions as data is very powerful.

-- Let's start a small collection of useful generic functions.

id'  :  a -> a
id' x = x

-- This is also built into idris as id.

-- Let's now look at another function:
apply'  :  (a -> b) -> a -> b
apply' f x = f x

apply''  :  (a -> b) -> (a -> b)
apply'' f = f
-- or simply:
apply''' : (a -> b) -> (a -> b)
apply''' = id

-- Removing an argument from both sides of the definition 
-- is called η-contraction.

add3' : Nat -> Nat
add3' = add 3  

flip'  :  (a -> b -> c) -> (b -> a -> c)
flip' f x y = f y x

-- Note: '->' is right-associative, but function application 
-- is left-associative.
compose  :  (a -> b) -> (b -> c) -> a -> c
compose f g x = g (f x)  
-- a --f--> b --g--> c

-- Defined in the standard library as the infix (.).
compose_backward  :  (b -> c) -> (a -> b) -> a -> c
compose_backward f g x = f (g x)

-- Using compose:
compose_backward'  :  (b -> c) -> (a -> b) -> a -> c
compose_backward' = flip' compose


{-- Higher-Order Functions for Parameterized Types --}

-- We can use higher-order functions to perform
-- operations on data structures such as lists
-- that are typically done imperatively using loops.

-- list mapping:
--   Apply a function to each list element.
--
--    [x  ,  y  ,  z  , ...]
--     _     _     _     _
--    f|    f|    f|  ...|
--     V     V     V     V
--   [f x , f y , f z , ...]

map_list  :  (a -> b) -> List a -> List b
map_list f [] = []
map_list f (x :: xs) = f x ::  map_list f xs


-- Examples:
map_successor : List Nat -> List Nat
map_successor xs = map_list (S) xs

map_add3 : List Nat -> List Nat 
map_add3 = map_list (add3)

-- This was defined in Lecture 2.
is_even  :  Nat -> Bool
is_even Z  =  True
is_even (S n)  = not (is_even n)

map_isEven : List Nat -> List Bool
map_isEven xs = map_list is_even xs

--       1    :: (2    :: (3    :: []))
--       _        _        _        _
-- isEven|  isEven|  isEven|  isEven|
--       V        V        V        V
--     False :: (True :: (False  :: []))

-- list filtering:
--   Keep only those list elements that satisfy a predicate.

filter_list  :  (a -> Bool) -> List a -> List a
filter_list p [] = []
filter_list p (x :: xs) = case p x of
    False => filter_list p xs
    True => x :: filter_list p xs

-- Example using flip:
evens  :  List Nat -> List Nat
evens xs = filter_list is_even xs


-- zip list:
-- The function map_list lets us apply a function to a list 
-- of arguments and get a list of results. We can do the 
-- same thing for functions that take two arguments:

--     [x0    ,   x1    ,   x2   ,  ...]
--     [y0    ,   y1    ,   y2   ,  ...]
--       _         _         _       _
--      f|        f|        f|    ...|
--       V         V         V       V
--   [f x0 y0 , f x1 y1 , f x2 y2 , ...]

-- We call this function zip:
zip_list  :  (a -> b -> c) -> List a -> List b -> List c
zip_list f [] [] = []
zip_list f [] (y :: ys) = []
zip_list f (x :: xs) [] = []
zip_list f (x :: xs) (y :: ys) = f x y :: zip_list f xs ys

-- Examples for list zipping:

zip_plus : List Nat -> List Nat -> List Nat
zip_plus xs ys = zip_list (add) xs ys

pair_list  :  List a -> List b -> List (Pair a b)
pair_list xs ys = zip_list MkPair xs ys


{-- Function Literals --}

-- We have literal expressions for strings ("hi") and numbers (7).
-- Idris provides literal expressions for functions as well.
-- (You may sometimes find them as annonymous functions).

-- Recall the definition of add3:
-- add3 : Nat -> Nat
-- add3 x = 3 + x

-- Redefine map_add3 without calling add3.
map_add3' : List Nat -> List Nat 
map_add3' xs = map_list (\x => 3 + x) xs

-- The syntax comes from the λ-calculus:

-- Redefine zip_plus:
zip_plus' : List Nat -> List Nat -> List Nat
zip_plus' xs ys = zip_list (\x, y => x + y) xs ys
-- zip_plus' xs ys = zip_list (\x => \y => x + y) xs ys

-- Syntax: for f : a_1 -> ... -> a_{n-1} -> a_n:
-- \a_1, ..., a_{n-1} => f(a_1, ..., a_{n-1}).


{-- Folds --}

-- This is also called an "iterator" or "simple recursor" and is a 
-- "most generic" function in the sense that it encode or replaces 
-- the pattern-matching in the definition.

-- The fold for a type replaces its constructors with functions.

-- To write the type of the fold function for an inductive type:
-- (1) Examine the types of its element constructors:
--       [] : List a
--       (::) : a -> List a -> List a
-- (2) In each constructor replace the type itself
--     with a parameter type t:
--       n : t
--       c : a -> t -> t
-- (3) To write the type of the fold function
--     provide one argument for each constructor-replacing term
--     and return a function from the type being folded
--     to the parameter type t:
fold_list  : (n : t) -> (c : a -> t -> t) -> List a -> t

-- To write the definition of the fold function:
-- (1) Case split on the argument of type being folded.
-- (2) For each constructor of the type
--     apply the corresponding constructor-replacing term,
--     and recurse on each subterm of the parameter type:
fold_list n c [] = n
fold_list n c (x :: xs) = c x (fold_list n c xs)

-- This has the effect of transforming
-- a term of a List type
-- by replacing each occurrence of (::) with c
-- and replacing each occurrence of [] with n;
-- thereby turning it into a term of type t with the same "shape".

-- Using folds, we can write functions from inductive types
-- with no pattern-matching nor recursion:

fold_sumList : List Nat -> Nat
fold_sumList xs = fold_list 0 (add) xs

-- How does this work, intuitively?

--   ::                       +
--  /  \                     / \
-- 1    ::                  1   +
--     /  \                    / \
--    2    ::                 2   +
--        /  \                   / \
--       3    []                3   0


-- Define map_list using fold_list:
-- (with saturated arguments):
map_list'  :  (a -> b) -> List a -> List b
map_list' f xs = fold_list [] (\head, rec => f head :: rec) xs

-- (as a higher-order function) 
map_list''  :  (a -> b) -> List a -> List b
map_list'' f  = fold_list [] (\x, xs => f x :: xs) 

-- fold_nat:

-- data  Nat : Type  where
--   Z  :  Nat
--   S  :  Nat -> Nat

-- (2) Replace with:
-- z : t
-- s : t -> t

-- (3) Type of fold_nat:
fold_nat : (z : t) -> (s : t -> t) -> Nat -> t
fold_nat z s Z = z
fold_nat z s (S k) = s (fold_nat z s k)
-- Definition of fold_nat:


-- Example (define addition with fold):
-- add  :  Nat -> Nat -> Nat
-- add Z n  =  n
-- add (S p) n  =  S (add p n)
add' : Nat -> Nat -> Nat
add' m n = fold_nat n (S) m
