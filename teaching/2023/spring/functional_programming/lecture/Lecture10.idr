{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 10, 2023-04-03
 -- 
 -- Computation in Types
 --}

module Lecture10

import Data.Vect


{-- Type Expressions --}

-- In a dependently typed language types are ordinary data.
-- This means that we can write expressions that compute types.


-- A nullary operation on a type is just an element of that type:
nullary_op  :  Type -> Type
nullary_op a  =  a


-- A unary operation on a type is a function from that type to itself:
unary_op  :  Type -> Type
unary_op a  =  a ->  nullary_op a
-- unary_op a  =  a -> a


-- A binary operation on a type is a two-argument function on it:
binary_op  :  Type -> Type
binary_op a  =  a -> unary_op a
-- binary_op a  =  a -> (a -> a)


-- We can spot a pattern here:
-- A (S n)-ary operation on a type
-- is a function from that type
-- to the type of n-ary operations on that type:
ary_op  :  Nat -> Type -> Type
ary_op Z a  =  a
ary_op (S n) a  =  a -> ary_op n a


-- letting us rewrite the types of our n-ary operations above:
str  :  0 `ary_op` String
str = "hello"

rev  :  1 `ary_op` String
rev  =  reverse

cat  :  2 `ary_op` String
cat  =  (++)

-- In these definitions we need to *evaluate* an expression
-- in order to determine the type.



{-- Computation in Types --}

-- To typecheck the above expressions Idris had to evaluate expressions *in the types*.

-- Idris can evaluate expressions in types provided that:
-- * they are *total* (typechecking shouldn't crash or hang),
-- * if imported from another module, the visibility is *public export*.



{-- Filtering Vectors --}

-- The filter function for Vects must be a *dependent function*
-- because the result type depends on the argument value.

-- This illustrates a common pattern:
-- to write a dependent function we often need to
-- first write the function that computes its type.

accepts  :  (a -> Bool) -> Vect n a -> Nat
accepts p []  =  0
accepts p (x :: xs)  =  (if p x then S else id) (accepts p xs)
	-- case p x of
	-- 	False => id
	-- 	True => S
	-- $ (accepts p xs)

-- first attempt, something interesting goes wrong:
filter_vect'  :  (p : a -> Bool) -> (xs : Vect n a) -> Vect (accepts p xs) a
filter_vect' p []  =  []
filter_vect' p (x :: xs)  =  case p x of
	False => ?type_error_1 -- filter_vect' p xs
	True => ?type_error_2 -- x :: filter_vect' p xs


-- The terms that we wrote have the right types, but Idris can't see this.
-- Idris computes types for each clause.

-- Using `with` we can pattern match on any expression of an inductive type
-- on the *left side* of a definition clause.
-- In each subclause the matched expression will be replaced by the corresponding value.

filter_vect  :  (p : a -> Bool) -> (xs : Vect n a) -> Vect (accepts p xs) a
filter_vect p []  =  []
filter_vect p (x :: xs)  with (p x)
	_ | False  =  filter_vect p xs
	_ | True  =  x :: filter_vect p xs



{-- A Well-Typed printf Function --}

-- Many programming languages have some version of a `printf` function.
-- It takes a *format string* argument that contains both literal text
-- and *formatting directives* (written "%s", "%d", etc.)
-- that specify the number and order of subsequent typed arguments.

-- In Idris we can write `printf` as an ordinary *dependent function*,
-- without the need for any special compiler support.

-- Both the type and the value of the `printf` function
-- are computed from the format string.

-- For example:
--    printf ""  :  String
--    printf "hello"  :  String
--    printf "hello %s" :  String -> String
--    printf "hello %s %d" :  String -> Integer -> String

-- Plan:
--                          format string
--                                |
--                                | parse
--                                v
--                       format specification
--                            /         \
--                           /  compute  \
--                          v             v
--                       printf   :   PrintfType

-- Task 1:
-- Define an inductive type to represent *format specifications*,
-- i.e. the things represented by format strings.

-- Format strings are finite sequences, so we can take format specifications
-- to be lists of individual format specifiers.

-- Our *format specifiers* need to be able to represent:
-- * string literals (e.g. "hello")
-- * string parameters (using "%s")
-- * number parameters (using "%d")

data  FormatSpec : Type  where
	Lit  :  String -> FormatSpec
	Str  :  FormatSpec
	Num  :  FormatSpec


-- Task 2:
-- Define a function to parse a format string into a format specification.

-- We'll use a List of Chars because String is not an inductive type in Idris.
parse_format  :  List Char -> List FormatSpec
parse_format []  =  []
parse_format ('%' :: 's' :: chars)  =  Str :: parse_format chars
parse_format ('%' :: 'd' :: chars)  =  Num :: parse_format chars
parse_format (char :: chars)  =  -- Lit (cast char) :: parse_format chars
	case parse_format chars of
		(Lit next :: fs) => Lit (cast char ++ next) :: fs
		rec =>  Lit (cast char) :: rec


-- We can make it act on Strings by composing with `unpack`:
parse_format_string  :  String -> List FormatSpec
parse_format_string  =  parse_format . unpack


-- Task 3:
-- Define a function for turning a format specification
-- into the String-valued function type that it represents (cf: `ary_op`):
FormatType  :  List FormatSpec -> Type
FormatType []  =  String
FormatType (Lit str :: fs)  =  FormatType fs
FormatType (Str :: fs)  =  String -> FormatType fs
FormatType (Num :: fs)  =  Integer -> FormatType fs


-- Composing with `parse_format_string` computes the type
-- of the `printf` function for a given format string:
PrintfType  :  String -> Type
PrintfType  =  FormatType . parse_format_string


-- Task 4:
-- Define a dependent function that takes a format specification
-- to the formatting function of the corresponding FormatType.

-- If we try to do this by structural recursion we get stuck:
format_function'  :  (fs : List FormatSpec) -> FormatType fs
format_function' []  =  ""
format_function' (Lit str :: fs)  =  ?stuck1
format_function' (Str :: fs)  =  \ s => ?stuck2
format_function' (Num :: fs)  =  \ n => ?stuck3


-- We can solve this problem by adding an *accumulator* argument
-- that contains the part of the string that is determined so far.
-- In each recursive clause we say how the accumulator string gets updated.
-- When we reach the Nil clause we will have determined the entire string.
format_function_acc  :  (acc : String) -> (fs : List FormatSpec) -> FormatType fs 
format_function_acc acc []  =  acc
format_function_acc acc (Lit str :: fs)  =  format_function_acc (acc ++ str) fs
format_function_acc acc (Str :: fs)  =  \ s => format_function_acc (acc ++ s) fs
format_function_acc acc (Num :: fs)  =  \ n => format_function_acc (acc ++ show n) fs


-- The format function just calls this function with an empty accumulator:
format_function  :  (fs : List FormatSpec) -> FormatType fs
format_function  =  format_function_acc ""


-- Task 5:
-- Finally, the printf function is the format function
-- applied to the format specification list parsed from the format string:
printf  :  (s : String) -> PrintfType s
printf s  =  format_function (parse_format_string s)



-- This printf is just an ordinary dependent function
-- that is guaranteed to be well-typed
-- and requires no special compiler support!
