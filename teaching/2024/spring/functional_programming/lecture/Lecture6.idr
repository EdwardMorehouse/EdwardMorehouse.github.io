{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 6 (2024-02-26)
 -- 
 -- Monadic IO
 --}


module Lecture6

import Data.String  --  for parsing numbers
import System.File  --  for file IO


{-- Executing Statements vs. Evaluating Expressions --}

-- In imperative programming languages *executing a statement*
-- causes a change of state.

-- In purely functional programming languages we have statements
-- only for tasks like importing modules.

-- But *evaluating an expression* does not cause anything to happen,
-- so how can we make things happen in a functional language?


{-- The IO Type Constructor --}

-- The `IO` type constructor is used to signify *computations*.
-- These expressions evaluate to instructions to the run-time system.

-- When a computation is *run* it may perform *actions*
-- that interact with the world.

-- An expression of type `IO a` represents computation that when run
-- performs some actions and then returns a result of type `a`.

-- The run-time system includes primitive computations for performing
-- actions like console, file, and network IO.


-- the hello world computation:
greet  :  IO Unit
greet  =  putStrLn "hello world!"

-- In order to run a computation and perform its actions
-- we must compile or `:exec` it.


{-- Monadic Combinators --}

-- We build compound computations from simpler computations
-- using two *monadic combinators*:
--
-- * pure  :  a -> IO a
--   This creates a trivial computation
--   that performs no actions and results in the given value.
--
-- * (>>=)  :  IO a -> (a -> IO b) -> IO b
--   This sequences computations by running first one
--   and passing the resulting value to the next one.

-- the hello world computation using the monadic combinators:
greet'  :  IO Unit
greet'  =  pure "hello world!" >>= putStrLn

-- greet the user by name:
meet_and_greet  :  IO Unit
meet_and_greet  =
	putStr "What's your name? " >>=
	\ _ => getLine >>=
	\ name => putStrLn ("Hello " ++ name ++ "!")


{-- Do Notation --}

-- There is syntactic sugar for writing sequences of computations
-- in an imperative-looking style.

meet_and_greet'  :  IO Unit
meet_and_greet'  =  do
	putStr "What's your name? "
	name <- getLine
	putStrLn ("Hello " ++ name ++ "!")

-- This may look like a block of imperative statements, but it's not.
-- Do notation is just syntactic sugar:
-- 
-- do
-- 	x <- computation1
-- 	y <- computation2
-- 	z <- computation3
-- 	...
-- 
-- is syntax for:
-- computation1 >>=
-- \ x => computation2 >>=
-- \ y => computation3 >>=
-- \ z => ...


{-- Returning Results from Computations --}

-- A computation that tries to get a number from the user:
try_number  :  IO (Maybe Integer)
try_number  =  do
	putStr "Please enter a number: "
	str <- getLine
	case parseInteger str of
		Nothing => pure Nothing
		Just num => pure (Just num)

-- We can optimize this by by pulling the `pure` out of the cases
-- and noticing that the case distinction is then superfluous:
try_number'  :  IO (Maybe Integer)
try_number'  =  do
	putStr "Please enter a number: "
	str <- getLine
	pure (parseInteger str)

-- which desugars to:
try_number''  :  IO (Maybe Integer)
try_number''  =
	putStr "Please enter a number: " >>=
	\ _ => getLine >>=
	\ str => pure (parseInteger str)

-- `:exec` doesn't display the result of running a computation.
-- We can see it by sequencing the computation with the function
-- `print` or `printLn`.

-- Just as we can *call a function* multiple times,
-- we can also *run a computation* multiple times.

-- A computation that gets a list of numbers from the user:
get_numbers  :  IO (List Integer)
get_numbers  =  do
	putStr "Please enter a number: "
	str <- getLine
	case parseInteger str of
		Nothing => pure []
		Just num => do
			nums <- get_numbers
			pure (num :: nums)


{-- Monadic Combinators Revisited --}

-- If we replace `IO` with the identity function in the types of the
-- monadic combinators we get the types of familiar functions:

pure'  :  a -> id a
pure' x  =  x

bind'  :  id a -> (a -> id b) -> id b
bind' x f  =  f x

-- Going the other way, we can "monadify" function composition:

komp  :  (a -> IO b) -> (b -> IO c) -> (a -> IO c)
komp f g x  =  pure x >>= f >>= g


-- We can transform either of two computations into a single computation
-- that when run returns the corresponding result:
eitherIO  :  Either (IO a) (IO b) -> IO (Either a b)
eitherIO (Left comp)  =  do
	result <- comp
	pure (Left result)
eitherIO (Right comp)  =
	comp >>= pure . Right

-- We can transform a list of computations into a single computation
-- that when run returns a list of results:
sequenceIO  :  List (IO a) -> IO (List a)
sequenceIO []  =  pure []
sequenceIO (x :: xs)  =  do
	head <- x
	tail <- sequenceIO xs
	pure (head :: tail)


-- Let's practice desugaring that:
-- (exercise to the reader)


{-- File IO --}

-- Read the contents of a text file:
read_file  :  (path : String) -> IO (Either FileError String)
read_file path  =  do
	result <- openFile path Read
	case result of
		Left error => pure $ Left error
		Right file => do
			result <- fRead file
			closeFile file
			pure result

-- There is a function called `readFile` in the `System.File` module
-- that does this for you.

-- Later we will learn how to use algebraic interfaces
-- to structure computations more elegantly
