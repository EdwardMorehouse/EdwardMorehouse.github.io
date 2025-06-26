{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 9 (2024-04-08)
 -- 
 -- Indexed Types and Dependent Functions
 --}


module Lecture9

import Data.Fin
import Data.Vect


-- An *indexed type* (family) or "dependent type" (family)
-- is a function from a type to `Type`:
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

-- Instead, we can write an indexed family of finite types:
--
--    --------------
--    Fin  :  Nat -> Type
-- so that
--    n  :  Nat
--    --------------
--    Fin n  :  Type
-- where `Fin n` is a type with exactly `n` elements.

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

-- In the standard library we have `implementation Num (Fin (S n))`.

-- `Fin` lets us make finite types with any number of elements.
Hour  :  Type
Hour  =  Fin 24


{-- Vect Types --}

-- `Fin` types are indexed by `Nat`,
-- where the index tells us the number of elements in the type.

-- We can also make family of finite sequence types indexed by `Nat`:
--
--    --------------
--    Vect  :  Nat -> Type -> Type
-- so that
--    n  :  Nat
--    a  :  Type
--    -----------------
--    Vect n a  :  Type
-- where `Vect n a` is a type of length 'n' sequences of `a`s.

data  List' : (a : Type) -> Type  where
	LNil  :  List' a
	LCons :  a -> List' a -> List' a

data  Vect' : (len : Nat) -> (a : Type) -> Type  where
	VNil  :  Vect' Z a
	VCons :  a -> Vect' len a -> Vect' (S len) a

-- In the standard library vectors overload the constructor names
-- `Nil` and `(::)` and sequence notation `[ ... ]`.
-- (the function `the` and command `:set showtypes` may be useful)

-- In many ways, `Vect`s behave like `List`s.
-- Often we can even use the same algorithms for writing functions.

-- Generate constant sequence of a given length:
constant_list  :  a -> Nat -> List a
constant_list x Z  =  []
constant_list x (S n)  =  x :: constant_list x n

-- A more expressive type lets us give a more precise specification,
-- and now Idris can write the function for us:
constant_vect  :  a -> (n : Nat) -> Vect n a
constant_vect x Z  =  []
constant_vect x (S n)  =  x :: constant_vect x n

-- Recall from lecture 4,
-- the unsatisfactory cases that came up when we zipped `List`s:
zip_list  :  (a -> b -> c) -> List a -> List b -> List c
zip_list f [] []  =  []
zip_list f [] (y :: ys)  =  []  -- unsatisfactory
zip_list f (x :: xs) []  =  []  -- unsatisfactory
zip_list f (x :: xs) (y :: ys)  =  f x y :: zip_list f xs ys

-- They don't come up when we zip `Vect`s of the same length:
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

-- Sometimes we can avoid using `Maybe` in the result type
-- by eleminating the possibility of failure.

-- Recall from lecture 3,
-- we return a `Maybe` type because the index may be out of bounds:
index_list  :  Nat -> List a -> Maybe a
index_list i []  =  Nothing
index_list 0 (x :: xs)  =  Just x
index_list (S i) (x :: xs)  =  index_list i xs

-- By refining the argument types we can guarantee success:
index_vect  :  Fin n -> Vect n a -> a
index_vect FZ (x :: xs)  =  x
index_vect (FS i) (x :: xs)  =  index_vect i xs


{-- Tuple Types --}

-- The Pair type constructor lets us write a type
-- whose elements are ordered pairs of elements of other types:

nat_and_bool  :  Type
nat_and_bool  =  Nat `Pair` Bool

-- We can iterate this construction, but not uniquely:
nat_and_bool_and_string_l  :  Type
nat_and_bool_and_string_l  =  (Nat `Pair` Bool) `Pair` String

nat_and_bool_and_string_r  :  Type
nat_and_bool_and_string_r  =  Nat `Pair` (Bool `Pair` String)

-- This is pretty inconvenient.
-- Fortunately, we can define tuple types of any sequence of types:
--    n  :  Nat
--    ts  :  Vect n Type
--    ------------------
--    Tuple ts  :  Type

data  Tuple : (ts : Vect n Type) -> Type  where
	Nil  :  Tuple Nil
	(::) :  t -> Tuple ts -> Tuple (t :: ts)


-- To write the `index` for `tuple`s we need to compute the result type:
-- index_vect  :  Fin n -> Vect n a -> a
index_tuple  :  (i : Fin n) -> Tuple ts -> index_vect i ts
index_tuple FZ (x :: y)  =  x
index_tuple (FS i) (x :: y)  =  index_tuple i y

-- A *dependent function* is one where the type of the result
-- depends on the value of an arguement.


{-- Dependent Pair Types --}

-- A *dependent pair* type is a type of ordered pairs,
-- where the type of the second factor depends
-- on the value of the first factor.
--    a  :  Type
--    b  :  a -> Type
--    ------------------
--    DPair a b  :  Type

data  Pair' : (a : Type) -> (b : Type) -> Type  where
	MkPair'  :  a -> b -> Pair' a b

data  DPair' : (a : Type) -> (b : a -> Type) -> Type  where
	MkDPair'  :  (x : a) -> b x -> DPair' a b

-- In the standard library *DPair* is implemented differently,
-- but you should ignore that for now.

-- Warning: the syntactic sugar (x ** y) : (x : a ** b x)
-- means `MkDPair x y : DPair a b`
-- e.g.
-- DPair Bool (\ b => if b then Nat else String)

-- *DPair*s have projection functions like *Pair*s do:
fst'  :  DPair a b -> a
fst' (x ** y)  =  x

-- But the type of the second projection depends
-- on the value of the first:
snd'  :  (p : DPair a b) ->  b (fst' p)
snd' (x ** y)  =  y

-- We can use dependent pairs to package
-- an element of an indexed type together with its index.

-- A type of elements of a specified Fin type:
SomeFin  :  Type
SomeFin  =  DPair Nat Fin


{-- Dependent Functions --}

-- All of this is made possible by the *dependent function*
-- type constructor that is built into Idris.
--
-- Compare the type of non-dependent functions:
-- (->) : Type -> Type -> Type       (written a -> b)
-- with the type of dependent functions:
-- (->) : (a : Type) -> (b : a -> Type) -> Type  (written (x : a) -> b x)

