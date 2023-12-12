{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 6, 2023-03-06
 -- 
 -- Totality for Data and Codata
 --}

module Lecture6

import Data.Nat
import Data.Colist


-- Recall the inductive type of natural numbers:
data  Nat' : Type  where
	Z'  :  Nat'
	S'  :  Nat' -> Nat'

-- Idris functions, including constructors,
-- evaluate their arguments eagerly.

-- So every `Nat` is a finite term, `S (S (... (S Z)))`

three  :  Nat
three  =  S (1 + 1)


-- What if we try to write a term that is not finite?
badNat  :  Nat
badNat  =  S badNat



{-- Totality for Inductive Data --}

-- An expression of an inductive type is *total*
-- if it is:
-- (1) *covering*:
--      defined for every possible case, and
-- (2) *terminating*:
--      eventually yields a fully evaluated result.

-- * Coverage is easy to decide mechanically:
--   just check for all constructors.
-- * Termination is impossible to decide mechanically
--   (cf. the halting problem).

-- Idris uses a simple syntactic conservative approximation
-- to termination for functions on inductive types:
-- each recursive call must be on a proper subterm.


-- totality detected for inductive type Nat:
fact  :  Nat -> Nat
fact 0  =  1
fact (S n)  =  S n * fact n


-- non-totality suspected for inductive type Bool:
-- (from lecture 2)
stuck  :  Bool -> Void
stuck b  =  stuck (not b)


-- totality detected for inductive type Nat:
iterate  :  Nat -> (a -> a) -> a -> a
iterate 0 f  =  id
iterate (S n) f  =  iterate n f . f


-- totality not detected for inductive type Nat
-- due to syntactic nature of approximation:
fact'  :  Nat -> Nat
fact' 0  =  1
fact' (S n)  =  S n  * fact' (id n)



{-- Coinductive Data --}

-- For many programming tasks
-- (e.g. operating systems, servers, REPLs)
-- we don't want termination.

-- A *process* should keep running indefinitely,
-- but must remain responsive.

-- We call such types *coinductive data types*
-- or *codata types* for short.

-- A term of a codata type may be either finite or infinite.

-- In Idris we indicate that an expression is coinductive
-- by using a special type constructor `Inf`
-- with a single term constructor `Delay`*.
--                        *This is not exactly true

data  Inf' : (a : Type) -> Type  where
	Delay'  :  a -> Inf' a


-- the type of co-natural numbers:
data  Conat : Type  where
	Zero  :  Conat
	Succ  :  Inf Conat -> Conat


one  :  Conat
one  =  Succ (Delay Zero)

-- Idris can infer the `Delay`s for us:
-- if it encounters an expression of type `a`
-- where it expected one of type `Inf a`,
-- it will elaborate it with a `Delay`.

two  :  Conat
two  =  Succ one



{-- Evaluation Semantics of Delay --}

-- Because an expression of type `Inf a` is potentially infinite,
-- the expression `Delay exp` is treated specially by the runtime:
-- the argument `exp` is not evaluated.

-- So Idris evaluates an expression of type `Conat` only until
-- it discovers whether it is `Zero` or a `Succ (Delay ?n)`.

infinity  :  Conat
infinity  =  Succ infinity


-- Evaluation of expressions of `Inf` types is forced
-- by pattern matching, which removes the `Delay`.

pred  :  Conat -> Conat
pred Zero  =  Zero
pred (Succ (Delay n))  =  n


-- ...even when the `Delay`s are implicit:
pred'  :  Conat -> Conat
pred' Zero  =  Zero
pred' (Succ n)  =  n

still_infinity  :  Conat
still_infinity  =  iterate 10000 pred infinity



{-- Totality for Coinductive Data --}

-- An expression of a coinductive type is *total*
-- if it is:
-- (1) *covering*:
--      defined for every possible case, and
-- (2) *productive*:
--      eventually yields a (possibly `Delay`ed) result.

-- Like termination for inductive types,
-- productivity for coinductive types is generally undecidable.

-- Idris uses a simple syntactic conservative approximation
-- to productivity for expressions of coinductive type:
-- each recursive occurrence must be "guarded" by a constructor
-- (and thus by a `Delay`).


-- totality detected for coinductive type Conat:
add : Conat -> Conat -> Conat
add Zero n  =  n
add (Succ m) n  =  Succ (add m n)


double_infinity  :  Conat
double_infinity  =  add infinity infinity



-- totality detected (both tests succeed):
coN  :  Nat -> Conat
coN Z  =  Zero
coN (S n)  =  Succ (coN n)


implementation  Num Conat  where
	(+)  =  add
	(*)  =  ?times
	fromInteger  =  coN . fromInteger

-- Now we can use numerals for Conats.


-- non-totality suspected (both tests fail):
uncoN  :  Conat -> Nat
uncoN Zero  =  Z
uncoN (Succ n)  =  S (uncoN n)



badNat'  :  Nat
badNat'  =  uncoN infinity



-- For productivity to be detected by Idris
-- each recursive occurrence of an expression of a codata type
-- must be an *immediate* constructor argument.

-- totality not detected for coinductive type Conat
-- due to syntactic nature of approximation:
infinity'  :  Conat
infinity'  =  Succ (id infinity')



{-- Potentially Infinite Sequence Types --}

-- Recall the type of finite sequences:
data  List' : (a : Type) -> Type  where
	NilL  :  List' a
	ConsL  :  a -> List' a -> List' a

-- The type of potentially infinite sequences:
data  Colist' : (a : Type) -> Type  where
	NilC  :  Colist' a
	ConsC  :  a -> Inf (Colist' a) -> Colist' a

-- totality detected for coinductive type Colist Nat:
zeros  :  Colist Nat
zeros  =  0 :: zeros


-- totality detected for inductive type Nat:
take'  :  Nat -> Colist a -> List a
take' 0 xs  =  []
take' (S n) []  =  []
take' (S n) (x :: xs)  =  x :: take' n xs


-- totality detected for coinductive type Colist b:
map'  :  (a -> b) -> Colist a -> Colist b
map' f []  =  []
map' f (x :: xs)  =  f x :: map' f xs


-- totality not detected for coinductive type Colist Nat:
nats'  :  Colist Nat
nats'  =  0 :: map S nats'

-- Sometimes we can rewrite such definitions
-- so that Idris can detect totality:
nats  :  Colist Nat
nats  =  nats_from 0
	where
		nats_from  :  Nat -> Colist Nat
		nats_from n  =  n :: nats_from (S n)



-- The hailstone function:
--            ( n/2  if n is even
--  h (n)  =  <
--            ( 3n+1  if n is odd

h  :  Nat -> Nat
h n  with (n `mod` 2 == 0)
	_ | True  =  n `div` 2
	_ | False  =  3 * n + 1


-- The hailstone sequence:
--
--  hail (n)  =  [n , h (n) , h (h (n)) , ...]
--
-- We can stop if we ever reach 0 or 1,
-- because of the cycles (0) and (1 , 4 , 2)
hail  :  Nat -> Colist Nat
hail n  with (n < 2)
	_ | True = [n]
	_ | False = n :: hail (h n)


-- the hailstone sequence is finite for 17:
hail_seventeen  :  List Nat
hail_seventeen  =  take 13 (hail 17)


-- Currently, nobody knows whether
-- `hail n` is finite for every n.
-- 
-- Paul Erdős said about the Collatz conjecture:
-- "Mathematics may not be ready for such problems."
-- He also offered US$500 for its solution.
-- Jeff Lagarias stated that the Collatz conjecture
-- "is an extraordinarily difficult problem,
-- completely out of reach of present day mathematics."
--                                    - Wikipedia
