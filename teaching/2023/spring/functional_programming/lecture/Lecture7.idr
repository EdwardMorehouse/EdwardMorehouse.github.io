{-- 
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- week 7, 2023-03-13
 -- 
 -- Monadic I/O
 --}

module Lecture7

import Data.String  --  for parsing numbers
import System.File  --  for file I/O


{-- Executing Statements vs Evaluating Expressions --}

-- In imperative programming languages executing a statement
-- causes a change of state.
-- In purely functional programming languages we don't have statements,
-- only expressions.
-- Evaluating an expression does not cause anything to happen.
-- So how can we make things happen in a functional language?




{-- The IO Type Constructor --}

-- The IO type constructor is used to signify *computations*.
-- These are expressions that act as instructions to the run-time system.
-- When a computation is *run* it may perform *actions*
-- that interact with the world.

-- An expression of type  IO a  represents computation
-- that when run performs some actions
-- and then returns a result of type  a.

-- The run-time system includes some basic computations
-- for doing console, file, and network IO.


{-
We will start with two basic I/O functions:
    putStrLn : String -> IO ()
    getLine : IO String
-}


-- the hello world computation:
greet  :  IO Unit
greet = putStrLn "Hello world!"

-- In order to run a computation and perform its actions
-- we must compile or  :exec  it.


{-- Monadic Combinators --}

-- We build up compound computations using two *monadic combinators*:
--
-- * pure  :  a -> IO a
--   This creates a trivial computation
--   that performs no actions and returns the given value.
--
-- * (>>=)  :  IO a -> (a -> IO b) -> IO b
--   This sequences computations by running first one
--   and passing the resulting value to the next one.


-- the hello world computation using the monadic combinators:
greet'  :  IO Unit
greet' = pure "Hello world!" >>= putStrLn


-- (>>=)  :  IO a -> (a -> IO b) -> IO b
-- greet the user by name:
meet_and_greet  :  IO Unit
meet_and_greet = putStrLn "Please enter your name: " >>=
                \_ => getLine >>=
                \str => putStrLn ("Hello " ++ str)
                

{-- Do Notation --}

-- There is syntactic sugar for writing sequences of computations
-- in an imperative looking style.

meet_and_greet'  :  IO Unit
meet_and_greet' = do
                putStrLn "Please enter your name: " 
                str <- getLine 
                putStrLn ("Hello " ++ str)


-- This may look like a block of imperative statements, but it is not.
-- In a purely functional programming language there are no statements!
-- Do notation is just syntactic sugar:
-- 
-- do
-- 	x_1 <- computation_1
-- 	x_2 <- computation_2
-- 	x_3 <- computation_3
-- 	...
--  computation_n
-- 
-- is syntax for:
-- computation_1 >>=
-- \ x_1 => computation_2 >>=
-- \ x_2 => computation_3 >>=
-- \ x_3 => ... computation_n

-- Start with a computation, get the result of the computation, use it in
-- a second computation and so on.
-- While in do-notation, you bind the result of the computation at the beginning.

komp_do  :  (f : a -> IO b) -> (g : b -> IO c) -> (x : a) -> IO c
komp_do f g x = do 
                x1 <- f x  
                g x1

komp_bind  :  (f : a -> IO b) -> (g : b -> IO c) -> (x : a) -> IO c
komp_bind f g x = f x >>= g 

-- komp looks like a kind of "funny composition". Look for Kleisli composition.



{-- Returning Results from Computations --}

-- (>>=) : IO a -> (a -> IO b) -> IO b
-- Let's write a computation that gets a list of numbers form the user:
get_numbers  :  IO (List Integer)
get_numbers = putStrLn "Please enter a number: " >>=
             \_ => getLine >>=
             \str => case (parsePositive str) of
                        Nothing => pure []
                        (Just num) => get_numbers >>=
                        \rest => pure $ num :: rest

get_numbers' : IO (List Integer)
get_numbers' = do
            _ <- putStrLn "Please enter a number: " 
            str <- getLine 
            case (parsePositive str) of
                 Nothing => pure []
                 (Just num) => do 
                 rest <- get_numbers' 
                 pure (num :: rest)


-- By default :exec doesn't display the results of running a computation.
-- We can use the functions  print  or  printLn  to do so.
-- They have the following signature (not exactly true): 
-- printLn : a -> IO (), where a implements the Show interface.

-- More interesting ways to use the (>>=) operator:
sum_get_numbers : IO Integer
sum_get_numbers = get_numbers >>= (\xs => pure $ sum xs) 


print_sum : IO ()
print_sum = get_numbers >>= (\xs =>  pure $ sum xs) >>= printLn

main : IO ()
main = greet

{-
Executing a file: 
Option 1: 
Write a main of type IO Unit,
Type in the terminal idris2 [name of the file] -o [name of the executable],
Change directory to: build/exec,
Run with: ./[name of executable].


Option 2: (compiles only one function that we want, of type IO Unit)
Type in the REPL: :c [name of executable] [name of function],
Exit the REPL,
Change directory to: build/exec,
Run with: ./[name of executable].
-}


{-- File I/O --}

{-
Functions that we need: 
openFile : String -> Mode -> IO (Either FileError File)
closeFile : File -> IO ()
fRead : File -> io (Either FileError String)
-}

-- read the contents of a text file:
--             path to file    the contents of the file unless error
read_file  :  (path : String) -> IO (Either FileError String)
read_file path = do
                file <- openFile path Read 
                case file of
                     (Left err) => pure $ Left err
                     (Right x) => do
                     contents <- fRead x 
                     closeFile x
                     case contents of
                          (Left err) => pure $ Left err
                          (Right conts) => pure $ Right conts

-- f (g (h x))
-- f $ g $ h x

-- There is a convenient function in System.File.ReadWrite called readFile
-- that does this.

