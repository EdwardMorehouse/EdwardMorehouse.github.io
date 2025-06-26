{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 12 (2024-04-29)
 -- 
 -- First-Order Logic
 --}


module Lecture12

import Data.Nat
import Data.Fin
import Lecture10

%default total  --  to ensure proof validity


{-  Falsity  -}

-- In the propositions-as-booleans interpretation
-- we can assert not only that something is true,
-- but also that it is false:

two_is_three'  :  Bool
two_is_three'  =  2 == 3

-- In the propositions-as-types interpretation
-- how can we assert that a proposition is false?

two_is_three  :  Type
two_is_three  =  Equal 2 3
 
-- * Recall that we represent a proposition by a type and 
--   a proof of a proposition by an element of that type.
-- 
-- * One way to assert that a proposition is false
--   is to claim that there can be no proofs of it.
-- 
-- * A proposition with no proofs corresponds to
--   a type with no elements; i.e. an empty type.


-- Recall the empty type `Void` from lecture 2:
data  Void' : Type  where
	-- no element constructors!

-- Regarded as a proposition, `Void` is "false".

-- Writing a function from the `Void` type to another type
-- is trivial because there are no cases to consider.

-- (this is in the standard library as `void`)
trivial  :  Void -> a
trivial x  impossible

-- But writing functions to the `Void` type from another type
-- is possible only if:

-- (1) the function is not total:
partial
hopeless  :  Nat -> Void
hopeless n  =  hopeless (S n)

-- (2) the other type is also empty:
pointless  :  Fin 0 -> Void
pointless FZ  impossible
pointless (FS x)  impossible


{-  Negation as Refutation  -}

-- We use a total function to the empty type `Void` to express
-- the negation of the argument type interpreted as a proposition.
-- (this is in the Prelude as `Not`)
Not'  :  Type -> Type
Not' a  =  a -> Void

-- * An element of type `Not a` is a function sending
--   elements of type `a` to elements of type `Void`.
-- 
-- * But there are no elements of the empty type `Void`.
-- 
-- * So if this function is total then there can be
--   no elements of type `a` either.
-- 
-- * Thus `a` must be an empty type.
-- 
-- * If we interpret the type `a` as a proposition,
--   this means that it has no proofs.
-- 
-- * Which is what it means to assert that it is false.

two_not_three  :  Not (2 = 3)  -- i.e. Equal 2 3 -> Void
two_not_three Refl  impossible


-- The *principle of contradiction* ("principle of explosion"
-- or "ex falso quodlibet") asserts that from the combination
-- of a proposition and its negation we may conclude anything.

public export
contradiction  :  a -> Not a -> b
contradiction a_true a_false  =  void (a_false a_true)


{-  Negated Proropositions  -}

-- In the propsitions-as-booleans interpretation
-- we can use the boolean negation function to define
-- the predicate of a number bing odd:
public export
is_odd  :  Nat -> Bool
is_odd  =  not . is_even

-- In the propsitions-as-types interpretation
-- we can do the same thing using type-level negation:
public export
Odd  :  Nat -> Type
Odd  =  Not . Even

-- Of course, one is odd:
public export
one_odd  :  Odd 1  -- i.e. Even 1 -> Void
one_odd Z_even  impossible
one_odd (SS_even x)  impossible

-- We can show that the successor of an even number is odd
-- by induction on the assumption `Even n`:
public export
succ_even_odd  :  Even n -> Odd (S n)
succ_even_odd Z_even  =  one_odd
succ_even_odd (SS_even n_even)  =
	let
		IH = succ_even_odd n_even
	in
		IH . pp_even

-- We can show that the successor of an odd number is even,
-- but we can't pattern match on the assumption `Odd n`
-- because `Odd` is not an inductively defined type.
-- However, we can pattern match on its `Nat` index `n`:
public export
succ_odd_even  :  {n : Nat} -> Odd n -> Even (S n)
succ_odd_even {n = 0} zero_odd  =  contradiction Z_even zero_odd
succ_odd_even {n = 1} one_odd  =  SS_even Z_even
succ_odd_even {n = S (S n)} ssn_odd  =
	let
		IH = succ_odd_even {n = n} (ssn_odd . SS_even)
	in
		SS_even IH


-- Idris provides an interface for empty types:

interface  Uninhabited' (a : Type)  where
	uninhabited'  :  a -> Void

-- The standard library includes implementations of `Uninhabited`
-- for many types corresponding to false propositions.

-- The Uninhabited interface provides a method,
-- absurd : Uninhabited a => a -> b.
-- This is like the function `void` for the type `Void`,
-- but for arbitrary empty types.

obvious  :  Not (S Z = S (S Z))
-- obvious  =  uninhabited
-- or
obvious  =  absurd


{-- Logical Connectives and Quantifiers  --}

-- One way to characterize the meaning of a proposition
-- is to specify what constitutes a valid proof.

-- Conjunction:
-- A proof of the proposition  `a and b`
-- is a proof of the proposition `a`
-- together with a proof of the proposition `b`.
public export
And  :  (a : Type) -> (b : Type) -> Type
And  =  Pair

eg_and  :  (Even 2) `And` Not (7 = S 7)
eg_and  =  (SS_even Z_even , uninhabited)


-- Disjunction:
-- A proof of the proposition `a or b`
-- is either a proof of the proposition `a`
-- or else a proof of the proposition `b`.
public export
Or  :  (a : Type) -> (b : Type) -> Type
Or  =  Either

eg_or  :  (Even 2) `Or` (7 = S 7)
eg_or  =  Left $ SS_even Z_even


-- Implication:
-- A proof of the proposition `a implies b`
-- is a function sending any proof of the proposition `a`
-- to a proof of the proposition `b`.
public export
Implies  :  (a : Type) -> (b : Type) -> Type
Implies a b  =  a -> b

eg_implies  :  (7 = S 7) `Implies` (8 = S 8)
-- eg_implies  =  absurd
-- or
eg_implies path  =  cong S path


-- Existential Quantification:
-- A proof of the proposition asserting that some element
-- of the type `a` satisfies the predicate `p`
-- is an element `x` of type `a` together with
-- a proof of the proposition that `x` satisfies `p`.
public export
Some  :  (a : Type) -> (p : a -> Type) -> Type
Some  =  DPair

eg_some  :  Some Nat Even
eg_some  =  (2 ** SS_even Z_even)


-- Universal Quantification:
-- A proof of the proposition asserting that each element
-- of the type `a` satisfies the predicate `p`
-- is a function that given any element `x` of type `a`
-- produces a proof of the proposition that `x` satisfies `p`.
public export
Each  :  (a : Type) -> (p : a -> Type) -> Type
Each a p  =  (x : a) -> p x

-- recall from lab 10:
%hint
succ_larger  :  {n : Nat} -> LTE n (S n)
succ_larger {n = Z}  =  LTEZero
succ_larger {n = S n}  =  LTESucc succ_larger

eg_each  :  Each Nat $ \ n => Some Nat $ \ m => LTE n m `And` Not (n = m)
eg_each n  =  (S n ** (succ_larger , nope))
	where
		nope : Not (n = S n)
		nope path  impossible


-- The kind of constructive logic that this
-- propositions-as-types interpretation realizes
-- is called "intuitionistic logic".
