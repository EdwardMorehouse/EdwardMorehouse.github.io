{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 7 (2024-03-25)
 -- 
 -- Totality for Data and Codata
 --}


module Lecture7

import Data.Colist

-- Expressions that are *total* are safe to evaluate
-- in the sense that they won't crash or hang the runtime.


-- Recall the inductive type of natural numbers:
data  Nat' : Type  where
	Z'  :  Nat'
	S'  :  Nat' -> Nat'

-- Idris functions, including constructors,
-- evaluate their arguments eagerly.

-- So every `Nat` value is a finite term, `S (... (S Z)...)`
three  :  Nat
three  =  S (1 + 1)

-- What if we try to write a term that is not finite?
badNat  :  Nat
badNat  =  S badNat


{-- Totality for Inductive Data --}

-- An expression of an inductive type is *total* if it is:
-- (1) *covering*:
--      defined for every possible case, and
-- (2) *terminating*:
--      eventually yields a fully evaluated result.

-- * Coverage is easy to decide algorithmically:
--   check for each constructor or a pattern variable.
-- * Termination is impossible to decide algorithmically
--   (cf. the halting problem).

-- Idris uses a simple syntactic conservative approximation
-- to termination for functions on inductive types:
-- each recursive call must be on a proper subterm.

-- Use the REPL command `:total`  to check totality.


-- Totality detected for inductive type Nat:
fact  :  Nat -> Nat
fact Z  =  1
fact (S n)  =  S n * fact n

-- Non-totality suspected for inductive type Bool:
-- (from lecture 2)
stuck  :  Bool -> Void
stuck b  =  stuck (not b)

-- Totality not detected for inductive type Nat
-- due to syntactic nature of approximation:
fact'  :  Nat -> Nat
fact' Z  =  1
fact' (S n)  =  S n * fact' (id n)


{-- Coinductive Data --}

-- For many programming tasks (e.g. operating systems, servers, REPLs)
-- we don't want termination.

-- A *process* should keep running for as long as we want,
-- but must remain responsive.

-- We call such types *coinductive data types*
-- or *codata types* for short.

-- A term of a codata type may be either finite or infinite.

-- In Idris we indicate that an expression is coinductive
-- by using a special type constructor `Inf`
-- with a single element constructor `Delay`*.
--                        *This is not exactly true
data  Inf' : (a : Type) -> Type  where
	Delay'  :  a -> Inf' a

-- The element constructor `Delay'` provides an *isomorphism*
-- between the types `a` and `Inf' a`.
-- 
-- The *inverse* of this type isomorphism is a function that goes
-- the other way*.
--                        *This is not exactly true
Force'  :  Inf' a -> a
Force' (Delay' x)  =  x

-- In the current Idris implementation, `Inf` is not
-- a type constructor with element constructor `Delay`.
-- Instead, `Inf` is a "type annotation" and `Delay` and `Force`
-- are "compiler primitives" (`:doc` them for details).


{-- Potentially Infinite Numbers --}

-- The coinductive type of co-natural numbers:
data  Conat : Type  where
	Zero  :  Conat
	Succ  :  Inf Conat -> Conat

one  :  Conat
one  =  Succ (Delay Zero)

-- Idris can infer the `Delay`s for us:
-- if it encounters an expression of type `a`
-- where it expected one of type `Inf a`,
-- it will elaborate it with a `Delay`:

two  :  Conat
two  =  Succ one


{-- Evaluation Semantics of Delay --}

-- Because an expression of type `Inf a` is potentially infinite,
-- the expression `Delay exp` is treated specially by the runtime:
-- the argument to `Delay` is not evaluated.

-- So Idris evaluates an expression of type `Conat` only until
-- it discovers whether it is `Zero` or a `Succ (Delay ...)`.

infinity  :  Conat
--infinity  =  Succ (Delay infinity)
infinity  =  Succ infinity

-- Evaluating expressions of coinductive types can progress
-- by pattern matching within a `Delay`:

-- bounded predecessor function:
pred'  :  Conat -> Conat
pred' Zero  =  Zero
pred' (Succ (Delay n))  =  n

-- Alternatively, instead of pattern-matching with `Delay`
-- on the left we can apply `Force` on the right:

pred''  :  Conat -> Conat
pred'' Zero  =  Zero
pred'' (Succ dn)  =  Force dn

-- Or we can just leave the `Delay`s and `Force`s implicit
-- because Idris can tell when it has a type mismatch  `a ~ Inf a`
-- and apply the corresponding isomorphism function for us:
pred  :  Conat -> Conat
pred Zero  =  Zero
pred (Succ n)  =  n

-- We can `:printdef` a definition to see its eloboration.

-- (from lab 4 & homework 2)
iterate  :  Nat -> (a -> a) -> a -> a
iterate 0 f  =  id
iterate (S n) f  =  f . iterate n f

still_infinity  :  Conat
still_infinity  =  iterate 100000 pred infinity

--https://www.youtube.com/watch?v=UUtvovhLIsQ


{-- Totality for Coinductive Data --}

-- An expression of a coinductive type is *total* if it is:
-- (1) *covering*:
--      defined for every possible case, and
-- (2) *productive*:
--      eventually yields a (possibly `Delay`ed) result.

-- Like termination for inductive types,
-- productivity for coinductive types is generally undecidable.

-- Idris uses a simple syntactic conservative approximation
-- to productivity for expressions of coinductive type:
-- each recursive occurrence must be *guarded* by a constructor
-- (and thus by a `Delay`).

-- Totality detected for coinductive type Conat:
add : Conat -> Conat -> Conat
add Zero n  =  n
--add (Succ m) n  =  Succ (Delay (add (Force m) n))
add (Succ m) n  =  Succ (add m n)

-- Totality detected (both tests succeed):
coN  :  Nat -> Conat
coN Z  =  Zero
--coN (S n)  =  Succ (Delay (coN n))
coN (S n)  =  Succ (coN n)

-- We can write a `Num` implementation for conatural numbers:
implementation  Num Conat  where
	(+)  =  add
	(*)  =  ?goal_for_you
	fromInteger  =  coN . fromInteger
	
-- Now we can write Conats using numerals.

-- Non-totality suspected (both tests fail):
uncoN  :  Conat -> Nat
uncoN Zero  =  Z
--uncoN (Succ n)  =  S (uncoN (Force n))
uncoN (Succ n)  =  S (uncoN n)

-- Indeed, this function may fail to yield a result:
badNat'  :  Nat
badNat'  =  uncoN infinity


{-- Potentially Infinite Sequences --}

-- Recall the type constructor of finite sequences:
data  List' : (a : Type) -> Type  where
	NilL  :  List' a
	ConsL :  a -> List' a -> List' a

-- The type constructor of potentially infinite sequences:
data  Colist' : (a : Type) -> Type  where
	NilC  :  Colist' a
	ConsC :  a -> Inf (Colist' a) -> Colist' a

-- `Colist` is in the standard library and supports the
-- syntactic sugar for sequence types `[x, y, ...]`.

-- Totality detected for coinductive type Colist Nat:
zeros  :  Colist Nat
--zeros  =  0  :: Delay zeros
zeros  =  0  :: zeros

-- Totality detected for inductive type `Nat`:
take'  :  Nat -> Colist a -> List a
take' 0 xs  =  []
take' n []  =  []
--take' (S n) (x :: xs)  =  x :: take' n (Force xs)
take' (S n) (x :: xs)  =  x :: take' n xs

-- Totality detected for coinductive type `Colist b`:
map'  :  (a -> b) -> Colist a -> Colist b
map' f []  =  []
--map' f (x :: xs)  =  f x :: Delay (map' f (Force xs))
map' f (x :: xs)  =  f x :: map' f xs

-- Totality not detected for coinductive type `Colist Nat`:
nats  :  Colist Nat
nats  =  0 :: map S nats

-- For productivity to be detected by Idris
-- each recursive occurrence of an expression of a codata type
-- must be an *immediate* constructor argument.

-- We can usually rewrite such definitions so that
-- Idris can detect the totality (see lab).

