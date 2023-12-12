{-- 
 -- Introduction to monadic IO in Idris
 -- (or similar typed purely functional programming language)
 -- 
 -- by Ed Morehouse
 --}

module MonadicIO

import Data.String -- for parsing numbers


-- The IO type constructor is used to signify *computations*.
-- These are expressions that act as instructions to the run-time system.
-- When a computation is run it may perform *actions* that interact with the world.

-- The run-time system includes some basic computations
-- for doing console, file, and network IO.


-- hello world:
greet  :  IO Unit
greet  =  putStrLn "hello world!"


-- In order to run a computation and perform its actions
-- we must compile or :exec it.


-- We build up compound computations using two monadic combinators:
-- * pure : a -> IO a
--   This creates a trivial computation
--   that performs no actions and returns the given value.
-- * (>>=) : IO a -> (a -> IO b) -> IO b
--   This sequences computations by running first one
--   and passing the resulting value to the next one.


-- hello world using the monadic combinators:
greet'  :  IO Unit
greet'  =  pure "hello world!" >>= putStrLn


-- greet the user by name:
meet_and_greet  :  IO Unit
meet_and_greet  =
	putStr "What's your name? " >>=
	const getLine >>=
	\ name => putStrLn ("Hello " ++ name ++ "!")


-- There is syntactic sugar for writing computations
-- in an inperative looking style
-- by sequencing them within a "do-block".

meet_and_greet'  :  IO Unit
meet_and_greet' =  do
	putStr "What's your name? "
	name <- getLine
	putStrLn ("Hello, " ++ name ++ "!")


-- Let's write a computation that gets a list of numbers form the user:
public export
get_numbers  :  IO (List Integer)
get_numbers  =  do
	putStr "Please enter a number: "
	str <- getLine
	case parseInteger str of
		Nothing => pure []
		Just num => do
			nums <- get_numbers
			pure (num :: nums)

