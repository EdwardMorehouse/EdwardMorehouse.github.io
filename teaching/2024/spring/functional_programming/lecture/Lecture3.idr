{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 3 (2024-02-05)
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
	-- a list of Bools is either empty:
	EmpBool  :  BoolList
	-- or it has a first Bool followed by a list of Bools:
	ExtBool  :  (head : Bool) -> (tail : BoolList) -> BoolList

-- This gets tedious pretty quickly because we need
-- a new list type for each possible element type.

-- We can try making a "generic list" type
-- but what would be the type of its elements?

data  GenList : Type  where
	EmpGen  :  GenList
	ExtGen  :  (head : ?Gen) -> (tail : GenList) -> GenList

-- In a language where types are data
-- we can write types that involve other types.

-- Instead of making `List` a type outright, we make it
-- a function that takes a type and produces a type.

-- We have seen that an *element constructor*
-- can take arguments to produce an element.
-- Similarly, a *type constructor* or *parameterized type (family)*
-- can take arguments to produce a type.

data  List' : (a : Type) -> Type  where
	Nil'  :  List' a
	Cons' :  (head : a) -> (tail : List' a) -> List' a

-- The List type constructor is in the standard library.
-- The Cons element constructor is written (::).
-- There is syntactic sugar to write lists as
-- comma separated sequences of elements between brackets [].


{-- Generic Functions --}

-- Let's write a length function for Lists.

length_ex  :  (0 a : Type) -> List a -> Nat
length_ex a Nil  =  0
length_ex a (x :: xs)  =  S (length_ex a xs)

-- The list length function doesn't depend on the list element type `a`.
-- Such functions are called *generic* or *parametric*.
-- We indicate this by annotating that argument with the *quantity* 0.

-- Indeed, the type argument is redundant because as soon as we provide
-- the next argument we will know the element type of the list
-- and thus what `a` must be.


{-- Implicit Arguments --}

-- An *implicit argument* to a function is one that we don't provide
-- but instead expect Idris to *infer* for itself.
-- We mark arguments as implicit by surrounding them with braces {}.

length_ie  :  {0 a : Type} -> List a -> Nat
length_ie Nil  =  0
length_ie (x :: xs)  =  S (length_ie xs)


{-- Implicit Binding --}

-- There is shorthand for generic implicit arguments:
-- Idris assumes that any lowercase unbound variable
-- in a type specification is a generic implicit argument
-- and *implicitly binds* it for you.

length_ii  :  List a -> Nat
length_ii []  =  0
length_ii (x :: xs)  =  S (length_ii xs)

-- Idris will display explicit bindings for implicit arguments
-- at the REPL with the command `:ti`.

-- The `length` function is in the standard library.

-- A generic function to concatenate lists:
concat'  :  List a -> List a -> List a
concat' Nil ys  =  ys
concat' (x :: xs) ys  =  x :: concat' xs ys

-- This is also in the standard library, :search for it.


{-- Pair Types --}

-- A parameterized type family for *ordered pairs*:
data  Pair' : (a : Type) -> (b : Type) -> Type  where
	-- an element of an ordered pair type is an element of the first type
	-- together with an element of the second type:
	MkPair'  :  a -> b -> Pair' a b

-- Warning: the syntactic sugar "(x , y) : (a , b)"
--   means MkPair x y : Pair a b

-- Because the *projection functions* are generic,
-- there is only one thing they can do:

fst'  :  Pair a b -> a
fst' (x , y)  =  x

snd'  :  Pair a b -> b
snd' (x , y)  =  y


{-- Maybe Types and Partial Functions --}

-- Sometimes we want to write a function, but for some arguments
-- there is no reasonable value we can give.
-- We call these *partial functions*.

bad_index  :  (i : Nat) -> List a -> a
bad_index i []  =  ?stuck
bad_index 0 (x :: xs)  =  x
bad_index (S i) (x :: xs)  =  bad_index i xs

-- A type constructor for possibly missing data:
data  Maybe' : (a : Type) -> Type  where
	-- an element is either an element of `a`:
	Just'  :  a -> Maybe' a
	-- or else it's a new element not in the type `a`:
	Nothing'  :  Maybe' a

-- We can use Maybe types to express partial functions: 
index  :  (i : Nat) -> List a -> Maybe a
index i []  =  Nothing
index 0 (x :: xs)  =  Just x
index (S i) (x :: xs)  =  index i xs


{-- Either Types --}

-- parameterized type family with elements
-- from either one type or another:
data  Either' : (a : Type) -> (b : Type) -> Type  where
	-- an element is either an element of the first type:
	Left'  :  a -> Either' a b
	-- or else it's an element of the second type:
	Right' :  b -> Either' a b

-- Either types can be used to signal exceptions.

-- Return the first element of a list (if any):
head'  :  List a -> Either String a
head' []  =  Left "empty list has no head"
head' (x :: xs)  =  Right x


{-- Type Isomorphisms --}

-- Sometimes there are multiple types that can be used
-- to encode the same information.

-- If the type `a` has m elements and the type `b` has n elements
-- then the type `Either a b` has (m + n) elements.

-- Question: what types can we use for `l` and `r` so that the type
-- `Either l r` has the same number of elements as `Bool`?

Bool'  :  Type
Bool'  =  Either Unit Unit

-- A *type isomorphism* between two types `a` and `b`
-- is a pair of back-and-forth functions:
-- f : a -> b  and  g : b -> a
-- so that:
-- * g (f x) = x  for any  x : a
-- * f (g y) = y  for any  y : b

-- Let's define a type isomorphism between `Bool` and `Bool'`:

f  :  Bool -> Bool'
f False  =  Left MkUnit
f True  =  Right MkUnit

g  :  Bool' -> Bool
g (Left MkUnit)  =  False
g (Right MkUnit)  =  True
