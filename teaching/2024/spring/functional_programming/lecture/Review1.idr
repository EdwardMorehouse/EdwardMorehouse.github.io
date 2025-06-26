{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 7 (2024-03-04)
 -- 
 -- Review 1
 --}


module Review1
import Data.Nat -- for mod


{-- Part 1: Q&A --}

-- Inductive types are "freely generated" by their element constructors:
data  Nat' : Type  where
	Z'  :  Nat'
	S'  :  Nat' -> Nat'

-- In contrast to element constructors, functions need not be injective:
next_even  :  Nat -> Nat
next_even n  =  if n `mod` 2 == 0 then n else S n

-- Currying transforms a function taking two arguments simultaneously
-- into one taking them sequentially:
curry'  :  {0 a , b , c : Type} -> (Pair a b -> c) -> (a -> (b -> c))
curry' f x y  =  f (x , y)

-- Uncurrying transforms a function taking two arguments sequentially
-- into one taking them simultaneously:
uncurry'  :  (a -> b -> c) -> (Pair a b -> c)
uncurry' f (x , y)  =  (f x) y

-- The quantity `0` means we promise not to use an argument:
id' : {0 a : Type} -> a -> a
id' x  =  x

-- Without it we can write non-generic functions: 
not_id  :  {a : Type} -> a -> a
not_id {a = Nat} x  =  0
not_id {a = Bool} x  =  False
not_id {a = _} x  =  x

-- We can use it with explicit arguments as well:
const'  :  a -> (0 _ : b) -> a
const' x y  =  x



{-- Part 2: Odds and Ends --}

-- Named patterns

-- Use `@` to name a pattern:
is_ordered  :  Ord a => List a -> Bool
is_ordered []  =  True
is_ordered [x]  =  True
is_ordered (x :: xs@(y :: zs))  =  x <= y && is_ordered xs


-- where bindings
-- https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html#where-clauses

-- Structurally recursive list reversal is okay, but inefficient:
reverse_list  :  List a -> List a
reverse_list []  =  []
reverse_list (x :: xs)  =  reverse_list xs ++ [x]

-- It's more efficient to use a local function
-- that takes an additional accumulator argument:
reverse_list'  :  List a -> List a
reverse_list' xs =  reverse_helper xs []
	where
		reverse_helper  :  List a -> List a -> List a
		reverse_helper [] ys  =  ys
		reverse_helper (x :: xs) ys  =  reverse_helper xs (x ::  ys)

-- `where` bindings are equivalent to `let` bindings: 
reverse_list''  :  List a -> List a
reverse_list'' xs =
	let
		reverse_helper  :  List a -> List a -> List a
		reverse_helper [] ys  =  ys
		reverse_helper (x :: xs) ys  =  reverse_helper xs (x ::  ys)
	in
		reverse_helper xs []


-- infix declarations
-- https://idris2.readthedocs.io/en/latest/reference/operators.html

-- An infix declaration has an optional association and a precedence:
infixl 10 ^

(^)  :  Nat -> Nat -> Nat
m ^ 0  =  1
m ^ (S n)  =  m * m^n


-- hiding names
-- https://idris2.readthedocs.io/en/latest/reference/pragmas.html#hide

