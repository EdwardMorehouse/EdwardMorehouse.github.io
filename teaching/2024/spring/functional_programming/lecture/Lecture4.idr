{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 4 (2024-02-12)
 -- 
 -- Function Literals and Higher-Order Functions
 --}


module Lecture4

import Lecture2


{-- Generic Higher-Order Functions --}

-- The idea of treating functions as data is very powerful.

-- Let's start a collection of useful generic functions.
-- By parametricity, they will be determined by their types.

-- the identity function:
id'  :  a -> a
id' x  =  x

-- the constant function function:
const'  :  a -> b -> a
const' x y  =  x

-- The function type constuctor (->) is right associative
-- so  "a -> b -> c"  means  a -> (b -> c).

-- Function application (juxtaposition) is left associative
-- so  "f g x"  means  (f g) x.

-- We can think of `const` as taking two arguments in sequence.
-- But we don't have to give it both arguments ("saturate" it).
-- We can give it only one argument, producing a constant function.

-- a constant function:
always_sunny  :  b -> String
always_sunny  =  const "sunny"


-- We can write functions that not only return functions as results,
-- but that take functions as arguments as well:

flip'  :  (a -> b -> c) -> b -> a -> c
flip' f y x  =  f x y


compose  :  (a -> b) -> (b -> c) -> a -> c
compose f g x  =  g (f x)

-- a -f-> b -g-> c

-- For cultural reasons, composition is often written
-- with the arguments flipped:
compose_backward  :  (b -> c) -> (a -> b) -> (a -> c)
compose_backward  =  flip compose

-- This is in the standard library as (.)
-- so (g . f) x  =  g (f x)

-- We can make an infix operator for forward composition:
(*)  :  (a -> b) -> (b -> c) -> (a -> c)
(*)  =  compose


-- The function that takes a function and an argument
-- and applies the function to the argument:
apply'  :  (a -> b) -> a -> b
(apply' f) x  =  f x

-- We can instead think of this as a function that takes a function
-- of arbitrary type and returns a function of the same type:
apply''  :  (a -> b) -> (a -> b)
apply'' f  =  f

-- Notice that this is just the identity function:
apply'''  :  (a -> b) -> (a -> b)
apply'''  =  id

-- Dropping the same last argument from both sides
-- of a definition is called η-contraction.

-- Apply is in the standard library as ($) (with a more general type)


{-- Higher-Order Functions for Parameterized Types --}

-- We can use higher-order functions to perform
-- operations on data structures such as lists
-- that are typically done imperatively using loops.

-- list mapping:
--   Apply the same function to each list element (SIMD).
--
--    [x  ,  y  ,  z  , ...]      :  List a
--     _     _     _     _
--    f|    f|    f|  ...|        :  a -> b
--     V     V     V     V
--   [f x , f y , f z , ...]      :  List b

map_list  :  (a -> b) -> (List a -> List b)
map_list f []  =  []
map_list f (x :: xs)  =  f x :: map_list f xs

even_list  :  List Nat -> List Bool
--even_list xs  =  map_list is_even xs  -- η-contracts to:
even_list  =  map is_even

-- This is in the standard library as `map`.


-- list filtering:
--   Keep only those list elements that satisfy a predicate.

filter_list  :  (a -> Bool) -> List a -> List a
filter_list p []  =  []
filter_list p (x :: xs)  =  case p x of
	False => filter_list p xs
	True => x :: filter_list p xs

just_evens  :  List Nat -> List Nat
--just_evens xs  =  filter_list is_even xs  -- η-contracts to:
just_evens  =  filter is_even

-- This is in the standard library as `filter`.


-- The map function lets us apply a given function
-- to a list of arguments and get a list of results.
-- We can do the same thing with functions
-- that take two arguments:
--     [x0    ,   x1    ,   x2   ,  ...]    :  List a
--     [y0    ,   y1    ,   y2   ,  ...]    :  List b
--       _         _         _       _
--      f|        f|        f|    ...|      :  a -> b -> c
--       V         V         V       V
--   [f x0 y0 , f x1 y1 , f x2 y2 , ...]    :  List c

zip_list  :  (a -> b -> c) -> (List a -> List b -> List c)
zip_list f [] []  =  []
zip_list f [] (y :: ys)  =  []  -- somewhat unsatisfactory
zip_list f (x :: xs) []  =  []  -- somewhat unsatisfactory
zip_list f (x :: xs) (y :: ys)  =  f x y :: zip_list f xs ys

zip_plus  :  List Nat -> List Nat -> List Nat
--zip_plus ms ns  =  zip_list (+) ms ns  -- η-contracts to:
zip_plus  =  zip_list (+)

-- We can zip a pair of lists into a list of pairs:
pair_list  :  List a -> List b -> List (Pair a b)
pair_list  =  zip_list MkPair

-- We can also split a list of pairs into a pair of lists:
unpair_list  :  List (Pair a b) -> Pair (List a) (List b)
unpair_list []  =  ([] , [])
unpair_list ((x , y) :: ps)  =
	let
		MkPair xs ys  =  unpair_list ps
	in
		(x :: xs , y :: ys)


{-- Currying and Uncurrying Functions --}

{- If we start with a list of pairs,
   unpair it with `unpair_list`
	 then re-pair them with `pair_list`
	 then we should get back the list we started with:

   [ (x0 , y0) , (x1 , y1) , (x2 , y2) , ... ]
     < unpair_list >
   ([x0 , x1 , x2 , ...] , [y0 , y1 , y2 , ...])
     < pair_list >
   [ (x0 , y0) , (x1 , y1) , (x2 , y2) , ... ]

   List (Pair a b) -ul-> Pair (List a) (List b) -pl-> List (Pair a b)
   But this doesn't work.  Why not?
 -}

unpair_then_pair_list  :  List (Pair a b) -> List (Pair a b)
unpair_then_pair_list  =  unpair_list * uncurry pair_list

-- We need to transform the pair_list function so that 
-- it takes its arguments simultaneously as a Pair
-- insead of sequentially as a higher-order function.

-- This function transformation is called "uncurrying":
uncurry'  :  (a -> b -> c) -> Pair a b -> c
uncurry' f (x , y)  =  f x y

-- The opposite function transformation is called "currying":
curry'  :  (Pair a b -> c) -> a -> b -> c
curry' f x y  =  f (x , y)


{-- Function Literals --}

-- We have literal expressions for strings ("hi") and numbers (7).
-- Idris provides literal expressions for functions as well.

drop  :  a -> b -> b
drop x y  =  y

-- The syntax for functiom literals comes from λ-calculus:
drop'  :  a -> b -> b
drop' x  =  \ y => y

-- There is an abbreviation for contracting successive bindings:
drop''  :  a -> b -> b
--drop''  =  \ x => \ y => y
drop''  =  \ x , y => y


{-- Section Notation --}

-- There is a clever extension to the syntax for infix operators.
-- Providing either operand determines a function that takes the other:

-- (  + 2)  means  \ x => x + 2
-- (2 +  )  means  \ y => 2 + y

-- Notice how these are just specializations of:

-- (  +  )  means  \ x , y => x + y


{-- Folds --}
public export
-- There is a "most general" function for each inductive type.
-- It is called the "iterator", "simple recursor", or "fold"
-- for that type.

-- To write the *type* of the fold function for an inductive type:
-- (1) Examine the types of the element constructors:
--       [] : List a
--       (::) : a -> List a -> List a
-- (2) In each constructor replace occurrences of the type itself
--     with a new parameter type t:
--       n : t
--       c : a -> t -> t
-- (3) To write the type of the fold function
--     provide one argument for each constructor-replacing variable
--     and return a function from the type being folded
--     to the new parameter type t:
fold_list  :  (c : a -> t -> t) -> (n : t) -> List a -> t

-- To write the *definition* of the fold function:
-- (1) Case split the argument of inductive type being folded.
-- (2) For each constructor of that type
--     apply the corresponding constructor-replacing term,
--     and recurse on each subterm of the parameter type t:
fold_list c n []  =  n
fold_list c n ((::) x xs)  =  c x (fold_list c n xs)

-- The fold for List types is in the standard library as `foldr`.

-- In the running example this has the effect of transforming
-- a term of type `List a` by:
-- * replacing each occurrence of (::) with c
-- * replacing each occurrence of [] with n.
-- This turns it into a term of type `t` with the same "shape":
--
--    x  y  z    []            x  y  z    n      
--    |  |   \  /              |  |   \  /       
--    |  |    ::               |  |    c         
--    |   \  /                 |   \  /          
--    |    ::         |->      |    c            
--     \  /                     \  /             
--      ::                       c               
--       |                       |               
--     List a                    t               
--
-- Using folds, we can write functions from inductive types
-- without using pattern-matching or recursion:

map_list'  :  (a -> b) -> List a -> List b
map_list' f  =  fold_list (\ h , t => f h :: t) []

