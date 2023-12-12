{-- 
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- week 16, 2023-05-15
 -- 
 -- Record Types
 --}

module Lecture16

import  Data.Vect


{-- Record Types --}

-- A *record type* is a type that collects together data of multiple other types.
-- Logically, record types are related to `Tuple` types and `DPair` types,
-- as well as to dictionary types and to inductive types with a single constructor.

-- Consider the following inductive type:
data  Name' : Type  where
	MkName'  :  (first , last : String) -> Name'

-- and its element:
my_name'  :  Name'
my_name'  =  MkName' "Ed" "Morehouse"

-- A record type has a single *constructor* and any number of *fields*:
record  Name  where
	constructor  MkName
	-- record fields:
	first :  String
	last  :  String

-- To create an element of a record type we apply the constructor function
-- to arguments corresponding to the record fields:
my_name  :  Name
my_name  =  MkName "Ed" "Morehouse"


-- Records come with some extra convenience features.

-- Idris automatically defines *projection functions* for record fields (getters):
my_first_name  :  String
my_first_name  =  first my_name

-- The projection functions may be written using *dot syntax*:
my_first_name'  :  String
my_first_name'  =  my_name.first


-- Defining a record type automatically generates a *namespace* for it,
-- so different record types can have the same field names.

record  Shirt  where
	constructor  MkShirt
	size  :  String
	-- etc.

record  Drive  where
	constructor  MkDrive
	size  :  Integer
	-- etc.

my_shirt  :  Shirt
my_shirt  =  MkShirt "Large"

my_drive  :  Drive
my_drive  =  MkDrive 1000



{-- Nested Records --}

-- Record fields can be of any type, including record types.

record  Contact  where
	constructor  MkContact
	name  :  Name
	email :  String


my_contact  :  Contact
my_contact  =  MkContact my_name "edmore@ttu.ee"


-- We can access nested fields by *iterated dot syntax*:

my_last_name  :  String
my_last_name  =  my_contact.name.last



{-- Record Updates --}

-- Record types have syntactic sugar for updating fields (setters).

-- We can copy an existing record, but provide a new value
-- for fields we choose using `:=`:
my_contact'  :  Contact
my_contact'  =  {email := "edward.morehouse@taltech.ee"} my_contact

-- If we want to compute the new value of a field from its old value
-- then we can apply a function using `$=`:
my_drive'  :  Drive
my_drive'  =  {size $= ( * 2)} my_drive



{-- Parameterized Records --}

-- Like inductive types, record types can take parameters:

-- compare the inductive pair type constructor:
data  Pair_i : (a , b : Type) -> Type  where
	MkPair_i  :  a -> b -> Pair_i a b

-- with the record pair type constructor:
record  Pair_r (a , b : Type)  where
	constructor  MkPair_r
	fst  :  a
	snd  :  b


my_stuff  :  Pair_r Shirt Drive
my_stuff  =  MkPair_r my_shirt my_drive'



{-- Dependent Records --}

-- In a *dependent record* the type of later fields
-- may depend on the value of earlier fields:

-- a dependent record type for finite sequences:
record  FiniteSequence (a : Type)  where
	constructor  Seq
	len  :  Nat
	val  :  Vect len a

seq1  :  FiniteSequence Bool
seq1  =  Seq 2 [False , True]

seq2  :  FiniteSequence Bool
seq2  =  {len $= S , val $= (True :: )} seq1


-- a dependent record type for Either types with any number of choices:
record  Choice {n : Nat} (options : Vect n Type)  where
	constructor  Pick
	idx  :  Fin n
	val  :  index idx options

my_choice  :  Choice [Nat , Bool , String]
my_choice  =  Pick 2 "hello"



-- In the standard library `DPair` is secretly a record type:
record  DPair' (a : Type) (b : a -> Type)  where
	constructor  MkDPair'
	fst  :  a
	snd  :  b fst


some_fin  :  DPair Nat Fin
some_fin  =  (3 ** 2)



{-- Interfaces are just Records --}

-- A record "interface" for numeric types:
record  Num' (ty : Type)  where
	constructor MkNum'
	-- like Num.(+):
	pls  :  ty -> ty -> ty
	-- like Num.(*):
	tms  :  ty -> ty -> ty
	-- like Num.fromInteger:
	int  :  Integer -> ty


-- turn a function into a constraint:
constrain  :  (a -> b) -> (x : a) => b
constrain f  =  f x

-- turn our record projection functions into "interface methods":

infixl 8 .+.
(.+.)  :  Num' ty => ty -> ty -> ty
(.+.)  =  constrain pls

infixl 9 .*.
(.*.)  :  Num' ty => ty -> ty -> ty
(.*.)  =  constrain tms

fromInteger'  :  Num' ty => Integer -> ty
fromInteger'  =  constrain int


-- a Nat "implementation" for our Num' "interface":
%hint
nat_implements_num  :  Num' Nat
nat_implements_num  =  MkNum' plus mult cast




{-- Go Further --}

-- TalTech (usually) offers a course in *type theory* in the fall term.

-- TalTech (usually) offers a course in *category theory* in the spring term.

-- We'll keep the *course Discord server* going through the summer.

-- There is an official *Idris Discord server* with a large active community.



{-- Thank You! --}

