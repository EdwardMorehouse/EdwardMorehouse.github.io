{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 5 (2024-02-19)
 -- 
 -- Programming Interfaces
 --}


module Lecture5


{-- Interfaces --}

-- When we treat a type *generically* in a function definition
-- we can't make any assumptions at all about that type
-- in exchange, we can apply the function to any type whatsoever

-- Sometimes we want to make assumpions about what a type could be
-- even though that restricts the arguments we can apply the function to.

-- An *interface* acts as a *constraint* on a collection of
-- type constructors ensuring that they can be used in some way.


-- The simplest form of interface acts on a sigle type.


{-- The Show Interface for Displayable Types --}

-- The `Show` interface is a constraint on a type
-- specifying that its elements have string representations:
interface  Show' (a : Type)  where
	show'  :  a -> String

-- The elements of an interface are called its *methods*.

-- The `show` method of the `Show` inteface provides
-- a string representation for elements of a type.

-- To implement an interface we define its methods for a given type.

-- A Show' implementation for Bools:
implementation  Show' Bool  where
	-- show'  :  Bool -> String
	show' False  =  "False"
	show' True  =  "True"

-- The `Show` interface and its `Bool` implementation
-- are already in the standard library.

-- You can `:doc` an interface to see its methods and implementations,
-- You can `:doc` a type (constructor) to see its interfaces,
-- You can `:search` for interface implementations.

-- A type for arithmetic expressions:
data  AExp : (a : Type) -> Type  where
	Val  :  a -> AExp a
	Plus  :  AExp a -> AExp a -> AExp a
	Times  :  AExp a -> AExp a -> AExp a

-- an arithmetic expression over booleans:
b_exp  :  AExp Bool
b_exp  =  (Val True `Plus` Val False) `Times` Val True


-- If we want to make a `Show` instance for arithmentic expressions
-- then we will need the *constraint* that the type `a` is showable:
implementation  (con : Show a) => Show (AExp a)  where
	-- show  :  AExp a -> String
	show (Val x)  =  show x
	show (Plus x y)  =  "(" ++ show x ++ " + " ++ show y ++ ")"
	show (Times x y)  =  "(" ++ show x ++ " * " ++ show y ++ ")"

-- Constraints are denoted by a double-shafted arrow:
-- <constraint> => <type>


{-- The Num Interface for Numberic Types --}

-- The reason that we're able to use Arabic numerals
-- and arithmetic operatiors for the types Nat, Integer, Double, etc.
-- is that they are all implement the `Num` interface:
interface  Num' (a : Type)  where
	(+~)  :  a -> a -> a
	(*~)  :  a -> a -> a
	fromInteger'  :  Integer -> a

-- We can make a Num implementation for Bool:
implementation  Num Bool  where
	-- (+)  :  Bool -> Bool -> Bool
	p + q  =  p || q
	-- (*)  :  Bool -> Bool -> Bool
	p * q  =  p && q
	-- fromInteger  :  Integer -> Bool
	fromInteger n  =  n > 0

b_val  :  Bool
b_val  =  (1 + 0) * 1

-- If we want to make a `Num` instance for arithmentic expressions
-- then we will need a `Num` *constraint* on the parameter type `a`:
implementation  Num a => Num (AExp a)  where
	-- (+)  :  AExp a -> AExp a -> AExp a
	(+)  =  Plus
	-- (*)  :  AExp a -> AExp a -> AExp a
	(*)  =  Times
	-- fromInteger  :  Integer -> AExp a
	fromInteger n  =  Val (fromInteger n)

-- Now we can express boolean arithmetic expressions very succinctly
b_exp'  :  AExp Bool
b_exp'  =  (1 + 0) * 1


{-- Specifying Types Explicitly --}

-- Within a program we usually provide enough type information
-- for Idris to infer the right interface implementations.

-- However in the interactive interpreter we usually don't provide
-- explicit type information and expect Idris to *infer* all types.

-- If Idris does not have enough type information it may *default*
-- to types different from the ones we intend and fail to choose the
-- interface implementation that we want.

-- We can explicitly provide Idris with type information using the 
-- standard library function:
the'  :  (0 a : Type) -> a -> a
the' a x  =  x

-- You can `:set showtypes` to see each value annotated with its type.


{-- Named Implementations --}

-- Interfaces act as constraints which should be uniquely satisfiable,
-- otherwise it's unclear which version of a method to use.

-- But sometimes we want to specify an alternative way in which
-- a type satisfies a constraint represented by an interface.
-- For this we use *named implementations* of interfaces.

-- A named implementation of the Show interface for natural numbers
-- that displays unary notation:
implementation  [unary] Show Nat  where
	-- show  :  Nat -> String
	show 0  =  ""
	show (S n)  =  "I" ++ show n

-- The syntax for invoking a named implementation is a bit clunky:
three  =  show @{unary} 3


{-- Multiple Constraints --}

-- We can express multiple costraints in
-- either curried or uncurried form:
implementation  [curried] Show a => Show b => Show (Pair a b)  where
	-- show  :  Pair a b -> String
	show (x , y)  =  "(" ++ show x ++ " , " ++ show y ++ ")"

implementation  [uncurried] (Show a , Show b) => Show (Pair a b)  where
	-- show  :  Pair a b -> String
	show (x , y)  =  "(" ++ show x ++ " , " ++ show y ++ ")"


{-- The Eq Interface for Comparable Types --}

interface  Eq' (a : Type)  where
	(==~)  :  a -> a -> Bool
	(==~) x y  =  not $ (/=~) x y
	(/=~)  :  a -> a -> Bool
	(/=~) x y  =  not $ (==~) x y

-- You can give *default implementations* of methods.
-- This is useful when some methods are definable from others.
-- In order to implement an interface you need to provide definitions
-- for at least a *basis* of its methods.

-- An `Eq` implementation for arithmetic expressions:
implementation  Eq a => Eq (AExp a)  where
	-- (==)  :  AExp a -> AExp a -> Bool
	(Val x) == (Val y)  =  x == y
	(Plus x z) == (Plus y w)  =  x == y && z == w
	(Times x z) == (Times y w)  =  x == y && z == w
	_ == _  =  False

-- We can determine how many times a value appears in a list
-- under the constraint that its element type is comparable:
multiplicity  :  Eq a => a -> List a -> Nat
multiplicity item []  =  0
multiplicity item (x :: xs)  =  case item == x of
	False => multiplicity item xs
	True => S $ multiplicity item xs


{-- The Ord Interface for Orderable Types --}

-- The elements of some types can be compared for ordering
-- as well as equality:
interface  Eq a => Ord' (a : Type)  where
	(<~) , (>~) , (<=~) , (>=~)  :  a -> a -> Bool
	min' , max'  :  a -> a -> a
	compare'  :  a -> a -> Ordering

-- We can check if a list is sorted:
is_sorted  :  Ord a => List a -> Bool
is_sorted []  =  True
is_sorted [x]  =  True
is_sorted (x :: y :: zs)  =  x <= y && is_sorted (y :: zs)

-- This is in the standard labrary as Data.List.sorted

-- We can also sort a list ourselves:
quicksort  :  Ord a => List a -> List a
quicksort []  =  []
quicksort (x :: xs)  =
	let
		lower  =  filter ( < x) xs
		upper  =  filter ( >= x) xs
	in
		quicksort lower ++ [x] ++ quicksort upper

-- There is a list-sorting function at `Data.List.sort`


{-- The Cast Interface for Type Conversions --}

-- Interfaces can be parameterized by more than a single type.

-- The interface for casting is parameterized by two types:
interface  Cast' (from , to : Type)  where
	-- methods
	cast'  :  from -> to


-- Now we can be like Python:
implementation  Cast Bool Nat  where
	-- cast  :  Bool -> Nat
	cast False  =  0
	cast True  =  1

implementation  Cast Nat Bool  where
	-- cast  :  Nat -> Bool
	cast 0  =  False
	cast (S n)  =  True


-- A cast from type `a` to type `b` is called *lossless*
-- if there is a function `undo : b -> a`
-- such that `(undo . cast) x == x` for any `x : a`.
-- A cast is *lossy* if it's not possible to undo.

