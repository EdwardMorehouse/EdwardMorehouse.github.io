{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 9, 2023-03-27
 -- 
 -- Indexed Types and Dependent Functions
 --}

module Lecture9

import Data.Fin
import Data.Vect


-- An *indexed type* (family) or "dependent type" (family)
-- is a function from a type to Type:
--    a  :  Type
--    ---------------
--    b  :  a -> Type

-- They let us specify a different type
-- for each element of the argument type:
--    x  :  a
--    ------------
--    b x  :  Type



{-- Fin Types --}

-- In lecture 2 we met a:
-- * 0-element type:  Void
-- * 1-element type:  Unit
-- * 2-element type:  Bool

-- We can define n-element types by hand, but we don't need to.

-- Instead we can write an indexed type:
--    n  :  Nat
--    --------------
--    Fin n  :  Type
-- so that Fin n is a type with exactly n elements.

-- We need a clever strategy for specifying these.

--                                     3,
--                             2,      2,
--                     1,      1,      1,
--             0.      0.      0.      0.    ...  :  Fin n
--    ---     ---     ---     ---     ---
--     0       1       2       3       4     ...  :  Nat

data  Nat' : Type  where
	NZ  :  Nat'
	NS  :  Nat' -> Nat'


data  Fin' : (n : Nat) -> Type  where
	FZ'  :  Fin' (S n)
	FS'  :  Fin' n -> Fin' (S n)



-- We can use numeric literals to refer to elements of Fin types.

-- Fin lets us make finite types with any number of elements.
Hour  :  Type
Hour  =  Fin 24



{-- Vect Types --}

-- Fin types are indexed by Nat,
-- where the index tells us the size of the Fin type.

-- We can also make finite sequence types indexed by Nat:
--    n  :  Nat
--    a  :  Type
--    -----------------
--    Vect n a  :  Type
-- where Vect n a is a sequence of n elements of a.

data  List' : (a : Type) -> Type  where
	LNil  :  List' a
	LCons :  a -> List' a -> List' a

data  Vect' : (n : Nat) -> (a : Type) -> Type  where
	VNil  :  Vect' Z a
	VCons :  a -> Vect' n a -> Vect' (S n) a

-- The standard library vectors overload the constructor names
-- and sequence notation.
-- (`:set showtypes` may be useful)

-- In many ways, Vects behave like Lists.
-- Often we can even use the same algorithms for writing functions.

-- Generate constant sequence of a given length:
constant_list  :  (n : Nat) -> a -> List a
constant_list Z x  =  []
constant_list (S n) x  =  x :: constant_list n x


-- By using a more expressive type, Idris can write it for us:
constant_vect  :  (n : Nat) -> a -> Vect n a
constant_vect Z x  =  []
constant_vect (S n) x  =  x :: constant_vect n x


-- Recall from lecture 4,
-- the unsatisfactory cases that came up when we zipped Lists:
zip_list  :  (a -> b -> c) -> List a -> List b -> List c
zip_list f [] []  =  []
zip_list f (x :: xs) []  =  []
zip_list f [] (y :: ys)  =  []
zip_list f (x :: xs) (y :: ys)  =  f x y :: zip_list f xs ys


-- They don't come up when we zip Vects of the same length:
zip_vect  :  (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zip_vect f [] []  =  []
zip_vect f (x :: xs) (y :: ys)  =  f x y :: zip_vect f xs ys


-- Recall from lecture 3,
-- we can write a list concatenation function:
concat_list  :  List a -> List a -> List a
concat_list [] ys  =  ys
concat_list (x :: xs) ys  =  x :: concat_list xs ys


-- We can concatenate vectors as well, once figure out the type:
concat_vect  :  Vect m a -> Vect n a -> Vect (m + n) a
concat_vect [] ys  =  ys
concat_vect (x :: xs) ys  =  x :: concat_vect xs ys

-- We will return to computation in types in earnest next week.

-- Sometimes we can avoid using Maybe in the return type
-- by eleminating the possibility of failure.

-- Recall from lecture 3,
-- we return a Maybe type because the index may be out of bounds:
index_list  :  Nat -> List a -> Maybe a
index_list i []  =  Nothing
index_list Z (x :: xs)  =  Just x
index_list (S i) (x :: xs)  =  index_list i xs


-- By using more expressive types we can guarantee success.
index_vect  :  Fin n -> Vect n a -> a
index_vect FZ (x :: xs)  =  x
index_vect (FS i) (x :: xs)  =  index_vect i xs


{-- Tuple Types --}

-- The Pair type constructor lets us write a type
-- whose elements are ordered pairs of elements of other types:

nat_and_bool  :  Type
nat_and_bool  =  Pair Nat Bool

nat_and_bool_and_string  :  Type
nat_and_bool_and_string  =  (Nat `Pair` Bool) `Pair` String

nat_and_bool_and_string'  :  Type
nat_and_bool_and_string'  =  Nat `Pair` (Bool `Pair` String)

-- This is pretty inconvenient.
-- We can define tuple types of any sequence of types:
--    n  :  Nat
--    ts  :  Vect n Type
--    ------------------
--    Tuple ts  :  Type

data  Tuple : (ts : Vect n Type) -> Type  where
	Nil  :  Tuple []
	(::) :  t -> Tuple ts -> Tuple (t :: ts)

-- index for tuples:
--index_vect  :  Fin n -> Vect n a -> a
index_tuple  :  (i : Fin n) -> Tuple ts -> index_vect i ts
index_tuple FZ (x :: xs)  =  x
index_tuple (FS i) (x :: xs)  =  index_tuple i xs



{-- Dependent Pair Types --}

-- A *dependent pair* type is a type of ordered pairs,
-- where the type of the second factor depends
-- on the value of the first factor.
--    a  :  Type
--    b  :  a -> Type
--    ------------------
--    DPair a b  :  Type

data  Pair' : (a : Type) -> (b : Type) -> Type  where
	MkPair'  :  (x : a) -> (y : b) -> Pair' a b


data  DPair' : (a : Type) -> (b : a -> Type) -> Type  where
	MkDPair'  :  (x : a) -> (y : b x) -> DPair' a b

-- Warning: the syntactic sugar (x ** y) : (x : a ** b x)
-- means MkDPair x y : DPair a b
-- e.g.
-- DPair Bool (\ b => if b then Nat else String)

-- We can use dependent pairs to package
-- an element of an indexed type together with its index.

-- A type of elements of a specified Fin type:
SomeFin  :  Type
SomeFin  =  (n : Nat ** Fin n)
--SomeFin  =  DPair Nat Fin



{-- Dependent Functions --}

-- All of this is made possible by the *dependent function*
-- type constructor that is built into Idris.
--
-- Compare the type of non-dependent functions:
-- (->) : (a : Type) -> (b : Type) -> Type       (written a -> b)
-- with the type of dependent functions:
-- (->) : (a : Type) -> (b : a -> Type) -> Type  (written (x : a) -> b x)

