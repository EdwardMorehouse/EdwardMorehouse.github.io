{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 2 (2024-01-29)
 -- 
 -- Inductive Types and Recursive Functions
 --}


module Lecture2


-- Idris comes with a few built-in types,
-- but also a powerful system for defining our own types.


-- the inductive type of booleans:
data  Bool' : Type  where
	-- list element( constructor)s:
	False' :  Bool'
	True'  :  Bool'

-- The Boolean type is already in the standard library
-- where it is called "Bool".

-- To define a function from a boolean
-- we want to know which boolean we are given.
-- We can do this using a *case expression*:
not_c  :  Bool -> Bool
not_c b  =  case b of
	False => True
	True => False

-- Case-analysing a function argument is very common.
-- There is a special syntax for this task called
-- definition by *pattern-matching*:
not_p  :  Bool -> Bool
not_p False  =  True
not_p True  =  False

-- Idris checks definitions for *coverage*,
-- and reports an error for missing cases.

-- Boolean negation is also in the standard library,
-- where it is called "not".

-- Let's write boolean conjunction by pattern matching.
and  :  Bool -> Bool -> Bool
and False False  =  False
and False True  =  False
and True False  =  False
and True True  =  True

-- Pattern matching uses *first-match semantics* where
-- * element constructors match only themselves,
-- * variables match anything, and get bound.
-- So we can use clause order to shorten definitions.
and'  :  Bool -> Bool -> Bool
and' True True  =  True
and' _ _  =  False

-- Boolean conjunction* is in the standard library
-- where it is called "(&&)".


-- The type Bool has exactly two elements.
-- Let's write a type that has exactly one element.
data  Unit' : Type  where
	-- list element( constructor)s:
	MkUnit'  :  Unit'

-- The Unit type is also in the standard library.
-- Warning: the syntactic sugar "() : ()" means MkUnit : Unit
-- I will use "()" to mean only MkUnit,
-- but the REPL uses it to mean Unit too.

-- Functions from the Unit type have only one case:
b_elt  :  Unit -> Bool
--b_elt u  =  False -- or
b_elt _  =  True

-- Functions to the Unit type have only one place to go:
erase  :  Bool -> Unit
erase _  =  MkUnit


-- Question: how many (mathematical) functions are there
-- from a type with m elements to a type with n elements?


-- We can also write a type that has exactly zero elements.
data  Void' : Type  where
	-- no element constructors!

-- The Void type is also in the standard library.

-- Functions from the Void type have no cases:
triv  :  Void -> Bool
triv v  impossible
--triv v  =  True
--triv v  =  False

-- Functions to the Void type have no place to go:
stuck  :  Bool -> Void
stuck b  =  stuck (not b)


{-- evaluation semantics:
    stuck True          | match stuck cl.1: b := True
 ~> stuck (not True)    | match not cl.1
 ~> stuck False         | match stuck cl.1: b := False
 ~> stuck (not False)   | match not cl.2
 ~> stuck True          | 
-}


-- The element constructors of a type can take parameters:
data  Shape : Type  where
	-- circle shape with given radius:
	Circle  :  (radius : Double) -> Shape
	-- rectangle shape with given width and height:
	Rectangle  :  (width : Double) -> (height : Double) -> Shape
	-- isosceles triangle with given base and height:
	IsosTriangle  :  (base : Double) -> (height : Double) -> Shape

-- Applying element constructors to create elements:
large_circle  :  Shape
large_circle  =  Circle 100

small_square  :  Shape
small_square  =  Rectangle 10 10


-- Pattern matching gives us access to
-- the element constructor arguments:
big_and_round  :  Shape -> Bool
big_and_round (Circle radius)  =  radius >= 20
big_and_round (Rectangle width height)  =  False
big_and_round (IsosTriangle base height)  =  False


-- Last time we made types with exactly 2, 1, and 0 elements.
-- Soon we will learn how to make types
-- with exactly n elements for any n.
-- For that we will need the type of natural numbers:
data  Nat' : Type  where
	-- zero is a natural number:
	Z'  :  Nat'
	-- the successor of a natural number is a natural number:
	S'  :  Nat' -> Nat'

-- This type is in the standard library
-- and has syntactic sugar for arabic numerals.

-- We can define natural number addition
-- by recursuion on the first argument:
add  :  Nat -> Nat -> Nat
-- 0 + n = n
add Z n  =  n
-- S m + n = S (m + n)
add (S m) n  =  S (add m n)

{-- evaluation semantics:
    add 2 p             | desugar 2
 ~> add (S (S Z)) p     | match add cl.2: m := S Z , n := p
 ~> S (add (S Z) p)     | match add cl.2: m := Z , n := p
 ~> S (S (add Z p))     | match add cl.1: n := p
 ~> S (S p)
--}

-- We can use a *let binding* to refer to the values
-- of expressions that we may want to use:
add'  :  Nat -> Nat -> Nat
add' Z n  = n
add' (S m) n  =
	let
		m_plus_n  =  add' m n
	in
		S m_plus_n

-- Nat addition is in the standard libray as "plus".
-- You can also use the infix operator "(+)".

-- A *predicate* is a proposition about a thing.
-- For now, a *proposition* will be a boolean.

public export -- allows the definition to be imported
-- the evenness predicate for natural numbers:
is_even  :  Nat -> Bool
is_even Z  =  True
is_even (S n)  =
	let
		n_is_even  =  is_even n
	in
		not n_is_even

-- The equality predicate (relation) for natural numbers:
nat_eq  :  Nat -> Nat -> Bool
nat_eq Z Z  =  True
nat_eq Z (S n)  =  False
nat_eq (S m) Z  =  False
nat_eq (S m) (S n)  =
	let
		m_is_n  =  nat_eq m n
	in
		m_is_n

-- This is in the standard library, :search!

