{-- 
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- week 15, 2023-05-08
 -- 
 -- Decidability and Automation
 --}

module Lecture15

import Data.Nat
import Data.List
import Data.Maybe
import Decidable.Equality

%default total  -- for proof validity


-- from lectures 11-14:
transport  :  (0 fam : a -> Type) -> {x , y : a} -> x = y -> fam x -> fam y
transport fam Refl = id

data  IsEven : (n : Nat) -> Type  where
	IsEvenZ  :  IsEven 0
	IsEvenSS :  IsEven n -> IsEven (S (S n))

IsOdd  :  Nat -> Type
IsOdd  =  Not . IsEven


-- Idris's *expression search* (proof search) algorithm
-- tries to build an expression of a specified type using
-- context variables, constructors, function literals, recursion,
-- default interface implementations, and search %hints.
--%hint
isEvenPP  :  IsEven (S (S n)) -> IsEven n
isEvenPP (IsEvenSS n_even)  =  n_even


-- if we %hint a definition then Idris will try it for proof (expression) search.
%hint
succ_even_is_odd  :  IsEven n -> IsOdd (S n)
succ_even_is_odd IsEvenZ  =  \ one_even => case one_even of
	_ impossible
succ_even_is_odd (IsEvenSS n_even)  =  succ_even_is_odd n_even . isEvenPP
	-- let
	-- 	IH = succ_even_is_odd n_even
	-- in
	-- 	IH . isEvenPP

%hint
succ_odd_is_even  : {n : Nat} -> IsOdd (n) -> IsEven (S n)
succ_odd_is_even {n = 0} zero_odd  =  void $ zero_odd IsEvenZ
succ_odd_is_even {n = 1} one_odd  =  IsEvenSS IsEvenZ
succ_odd_is_even {n = (S (S n))} ssn_odd  =
	IsEvenSS (succ_odd_is_even (ssn_odd . IsEvenSS))



{-  Decidable Propositions  -}

-- A logical proposition is called *decidable* if we can
-- either *affirm* it by providing a proof that it is true
-- or else *refute* it by providing a proof that it is false.

-- Under the *propositions-as-types* interpretation of logic this means
-- either producing an element of the given type,
-- or else showing that the type is empty by defining
-- a total function from it to the canonical empty type `Void`.

data  Decide  :  (proposition : Type) -> Type  where
	-- like True : Bool, but with evidence:
	Affirm  :  (prf : proposition) -> Decide proposition
	-- like False : Bool, but with evidence:
	Refute  :  (ref : Not proposition) -> Decide proposition


two_is_even  :  Decide (IsEven 2)
two_is_even  =  Affirm $ IsEvenSS IsEvenZ


four_is_not_five  :  Decide (2 + 2 = S 4)
four_is_not_five  =  Refute $ \ eq => case eq of
	Refl impossible


-- The Idris standard library has a version of
-- our `Decide` type constructor called `Dec`,
-- with constructors called `Yes` and `No`.



{-  Decidable Predicates  -}

-- A logical predicate is called *decidable* if we can decide
-- all of its instance propositions.

-- Under the *propositions-as-types* interpretation of logic this means
-- for a type family `p : a -> Type`
-- we have a function `(x : a) -> Dec (p x)`

-- A function that decides a predicate
-- is called a *decision procedure*.


-- a decision procedure for the `IsEven` predicate:
decide_even  :  (n : Nat) -> Dec (IsEven n)
decide_even 0  =  Yes IsEvenZ
decide_even (S n)  =  case decide_even n of
	Yes n_even => No (succ_even_is_odd n_even)
	No n_odd => Yes (succ_odd_is_even n_odd)



-- Once we have a decision procedure for a predicate, we no longer
-- need to write proofs of its instance propositions by hand.

-- is_four_even  =  decide_even 4

-- is_three_even  =  decide_even 3



{-  Decidable Equality  -}

-- A predicate that we often want to decide is equality.

-- lemma: the successor function is injective:
pred_equal  :  S m = S n -> m = n
pred_equal Refl =  Refl


-- a decision procedure for Nat equality:
decide_nat_eq  :  (m , n : Nat) -> Dec (m = n)
decide_nat_eq 0 0  =  Yes Refl
decide_nat_eq 0 (S n)  =  No uninhabited
decide_nat_eq (S m) 0  =  No uninhabited
decide_nat_eq (S m) (S n)  =  case decide_nat_eq m n of
	Yes m_n_equal => Yes $ cong S m_n_equal
	No m_n_differ => No $ m_n_differ . pred_equal


-- does_four_equal_four  =  decide_nat_eq (2 + 2) (2 * 2)

-- does_three_equal_four  =  decide_nat_eq 3 4


-- The module `Decidable.Equality` provides an interface
-- for types with decidable equality called `DecEq`
-- along with many common instances.



{-- Constraint Arguments --}

-- Recall that an *implicit argument* is written between braces `{n : Nat} -> ...`
-- Idris tries to infer implicit arguments using a *unification algorithm*
-- based on syntactic matching and recursion on subterms.
--   e.g.
--   Vect n Bool
--   Vect 3 a
--   -----------
--   n = 3 , a = Bool

-- In contrast, a *constraint argument* (also called an "auto implicit argument")
-- is different kind of implicit argument.
-- It is written using the double-shafted arrow `(n : Nat) => ...`
-- Idris tries to infer constraint arguments using the same *search algorithm*
-- used by the editor integration.

-- Finding an expression for a constraint argument is called
-- *satisfying* or *solving* the constraint.

list_head  :  (xs : List a) -> (nonempty : NonEmpty xs) => a
list_head [] impossible
list_head (x :: xs)  =  x



-- We can write a higher-order function
-- to turn any function that returns a `Maybe` result
-- into a function that returns a plain result
-- under the *constraint* that the function applied to the argument returns a `Just`:
constrain_just  :  (f : a -> Maybe b) -> (x : a) -> (is_just : IsJust (f x)) => b
constrain_just f x  with (f x)
	_ | Just y  =  y


-- e.g.
list_head'  :  (xs : List a) -> (IsJust (head' xs)) => a
list_head'  =  constrain_just head'


-- the dependent version of constrain_just:
constrain_just'  :  {b : a -> Type} ->
	(f : (x : a) -> Maybe (b x)) -> (x : a) -> (is_just : IsJust (f x)) => b x
constrain_just' f x  with (f x)
	_ | Just y  =  y



-- A longer example:
-- finding the square root of a perfect square

-- a predicate for perfect squares:
data  IsSquare : Nat -> Type  where
	SquareOf  :  (m : Nat) -> IsSquare (m * m)

-- e.g.:
four_is_a_square  :  IsSquare 4
four_is_a_square  =  SquareOf 2


-- It's easy to take the root a of a square:
root_of_square  :  IsSquare n -> Nat
root_of_square (SquareOf m)  =  m


-- takes a number and maybe proves it is a square:
search_square_root  :  (n : Nat) -> Maybe (IsSquare n)
search_square_root n = search_square_root_below n (S n)
	where
-- we know (but don't prove) that sqrt n < S n:
	search_square_root_below : (n , m : Nat) -> Maybe (IsSquare n)
	search_square_root_below n 0  =  Nothing
	search_square_root_below n (S m)  =  case decEq (m * m) n of
		Yes mm_n_equal => Just $ transport IsSquare mm_n_equal (SquareOf m)
		No mm_n_differ => search_square_root_below n m


find_square_root  =  constrain_just' search_square_root

-- return the square root of a number, under the constraint that it is a square:
square_root : (n : Nat) -> (is_square : IsJust (search_square_root n)) => Nat
square_root n  =  root_of_square $ find_square_root n

