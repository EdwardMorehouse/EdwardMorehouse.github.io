{-- 
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- week 3, 2023-02-13
 -- 
 -- Parameterized Types and Generic Functions
 --}

module Lecture3


{-- Parameterized Type Families --}

-- We can create an inductive type of lists
-- with a given element type:

data  NatList : Type  where
	-- a list of Nats is either empty:
	EmpNat  :  NatList
	-- or it has a first Nat followed by a list of Nats:
	ExtNat  :  (head : Nat) -> (tail : NatList) -> NatList

data  BoolList : Type  where
	EmpBool  :  BoolList
	ExtBool  :  (head : Bool) -> (tail : BoolList) -> BoolList

-- This gets tedious pretty quickly
-- because we need a new list type
-- for each possible element type.

-- We can try making a "generic list" type
-- but what would be the type of its elements?

data  GenList : Type  where
	EmpGen  :  GenList
	ExtGen  :  (head : ?gen) -> (tail : GenList) -> GenList


-- In a dependently typed language types are data.
-- So we can write expressions that involve types.

-- Instead of being a type, we can make lists
-- a function that takes a type and produces a type.
-- We call this a *type constructor* or
-- *parameterized type (family)*.
data  List' : (a : Type) -> Type  where
	Nil'  :  List' a
	Cons' :  (x : a) -> (xs : List' a) -> List' a

-- The List type constructor is in the standard library.
-- The Cons constructor is written (::).
-- There is syntactic sugar to write lists as
-- comma separated sequences of elements between brackets [].




{-- Generic Functions --}

-- Let's write a length function for Lists.
length_ex  :  (a : Type) -> List a -> Nat
length_ex a Nil  =  0
length_ex a (x :: xs)  =  S (length_ex a xs)


-- The length function doesn't care about
-- the element type of the list; i.e.
-- the algorithm doesn't depend on the argument `a`.
-- Such functions are called *generic*.

-- We only need the `a` in order to specify the function type.
-- Indeed, it is redundant because as soon as we give
-- the function an argument list it will know
-- the list element type and thus what `a` must be.




{-- Implicit Arguments --}

-- An *implicit argument* is one that we don't provide
-- but instead expect Idris to figure out for itself.
-- We mark implicit arguments by surrounding them with braces {}.

length_ie  :  {0 a : Type} -> List a -> Nat
length_ie []  =  0
length_ie (x :: xs)  =  S (length_ie xs)


-- We indicate that a function is *generic* in an implicit argument
-- by putting a *quantity* 0 in front of it.
-- This is like using an underscore `_` for an explicit argument.

-- There is syntactic sugar for generic implicit arguments:
-- Idris assumes that any lowercase unbound variable
-- is a generic implicit argument and implicitly binds it for you.

length_ii  :  List a -> Nat
length_ii []  =  0
length_ii (x :: xs)  =  S (length_ii xs)

-- Idris will show explicit bindings for implicit arguments
-- at the REPL with the command `:ti`.


-- A generic function to concatenate lists:
concat'  :  List a -> List a -> List a
concat' [] ys  =  ys
concat' (x :: xs) ys  =  x :: (concat' xs ys)




{-- Pair Types --}

-- A parameterized type family for *ordered pairs*:
data  Pair' : (a : Type) -> (b : Type) -> Type  where
	-- an element is a pair of both
	-- an element of `a` and an element of `b`:
	MkPair'  :  a -> b -> Pair' a b

-- Warning: the syntactic sugar (x , y) : (a , b)
--   means MkPair x y : Pair a b


-- Because the *projection functions* are generic,
-- there is only one thing they can do:
fst'  :  Pair a b -> a
fst' (x , y)  =  x

snd'  :  Pair a b -> b
snd' (x , y)  =  y




{-- Maybe Types and Partial Functions --}

-- Sometimes we want to write a function of type `a -> b`,
-- but there is not a reasonable result for some arguments:
bad_index  :  Nat -> List a -> a
bad_index i []  =  ?stuck
bad_index 0 (x :: xs)  =  x
bad_index (S i) (x :: xs)  =  bad_index i xs



-- A type constructor for possibly missing data:
data  Maybe'  :  (a : Type) -> Type  where
	-- an element is either an element of `a`:
	Just'  :  a -> Maybe' a
	-- or else it's a new element not in `a`:
	Nothing'  :  Maybe' a


-- We can use Maybe types to express this: 
index  :  Nat -> List a -> Maybe a
index i []  =  Nothing
index 0 (x :: xs)  =  Just x
index (S i) (x :: xs)  =  index i xs




{-- Either Types --}

-- parameterized type family elements
-- from either one type or another:
data  Either' : (a : Type) -> (b : Type) -> Type  where
	-- an element is either an element of `a`:
	Left'  :  a -> Either' a b
	-- or it's an element of `b`:
	Right' :  b -> Either' a b

-- Either types can be used to signal exceptions.

-- Return the first element of a list (if any):
head'  :  List a -> Either String a
head' []  =  Left "error: empty list"
head' (x :: xs)  =  Right x

