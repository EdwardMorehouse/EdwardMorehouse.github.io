{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 16 (2024-05-06)
 -- 
 -- Review 2
 --}


module Review2

import Data.Vect
import Syntax.PreorderReasoning
import Lecture11
import Lab11

%default total

{-- Examples and Q&A --}


-- Proving equalities:
%hint
plus_one_right  :  {n : Nat} -> n + 1 = S n
-- by equational reasoning:
plus_one_right  =  Calc $
	|~ n + 1
	~~ n + (S 0)     ...(cong (n + ) Refl)
	~~ S (n + 0)     ...(plus_succ_right)
	~~ S n           ...(cong S plus_zero_right)
-- by computation:
plus_one_right'  :  {n : Nat} -> n + 1 = S n
plus_one_right'  =  trans plus_succ_right (cong S plus_zero_right)
-- by structural induction:
plus_one_right''  :  {n : Nat} -> n + 1 = S n
plus_one_right'' {n = 0}  =  Refl
plus_one_right'' {n = S n}  =
	let
		IH = plus_one_right'' {n = n}
	in
		cong S IH

-- Using equalities:

-- from lab 11:
reverse_vect  :  {n : Nat} -> Vect n a -> Vect n a
reverse_vect []  =  []
reverse_vect (x :: xs)  =
	let
		rev  =  reverse_vect xs ++ [x]
	in
		transport (\ n => Vect n a) plus_one_right rev



-- Justifying proof steps:

-- multiplication distributes over addition on the left:
distl  :  {x , y , z : Nat} -> x * (y + z) = (x * y) + (x * z)
distl {x = 0}  =  Refl
distl {x = S x}  =  Calc $
	|~ S x * (y + z)
	~~ (x * (y + z)) + (y + z)        ...(times_succ_left)
	~~ ((x * y) + (x * z)) + (y + z)  ...(cong ( + (y + z)) distl)
	~~ (((x * y) + (x * z)) + y) + z  ...(?distl3)
	~~ ((x * y) + ((x * z) + y)) + z  ...(?distl4)
	~~ ((x * y) + (y + (x * z))) + z  ...(?distl5)
	~~ (((x * y) + y) + (x * z)) + z  ...(?distl6)
	~~ ((x * y) + y) + ((x * z) + z)  ...(?distl7)
	~~ (S x * y) + (S x * z)          ...(sym $ cong2 plus times_succ_left times_succ_left)


-- Functions for computing types:

accepts  :  (p : a -> Bool) -> (xs : Vect n a) -> Nat
accepts p []  =  0
accepts p (x :: xs)  =
	case p x of
		False => accepts p xs
		True => S $ accepts p xs

filter_vect'  :  (p : a -> Bool) -> (xs : Vect n a) -> Vect (accepts p xs) a
filter_vect' p []  =  []
filter_vect' p (x :: xs)  =  case p x of
	False => ?stuck1 -- filter_vect' p xs
	True => ?stuck2 -- x :: filter_vect' p xs


-- NOT ON THE EXAM (just useful to know):

-- In Idris the type of an expression remains constant within a clause.
-- So in order for the types to reduce we need to do the case split
-- on the left of the defining `=`.
-- In Idris we do this using `with` patterns:
-- https://idris2.readthedocs.io/en/latest/tutorial/views.html#the-with-rule-matching-intermediate-values

filter_vect  :  (p : a -> Bool) -> (xs : Vect n a) -> Vect (accepts p xs) a
filter_vect p []  =  []
filter_vect p (x :: xs) with (p x)
	_ | False  =  filter_vect p xs
	_ | True  =  x :: filter_vect p xs
