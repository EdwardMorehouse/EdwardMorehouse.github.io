{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 10 (2024-04-15)
 -- 
 -- Propositions as Types
 --}


module Lecture10

import Data.Nat  --  for LTE

%default total -- needed for proof validity

{-  Propositions as Booleans  -}

-- Up until now we have been representing predicates
-- as boolean-valued functions:
public export
is_even  :  Nat -> Bool
is_even 0  =  True
is_even (S n)  =  not (is_even n)

-- A *predicate* is a *proposition* about a thing.
-- So we have been representing propositions as booleans:

two_is_even  :  Bool
two_is_even  =  is_even 2

four_is_even  :  Bool
four_is_even  =  is_even 4

-- From the perspective of propositions as Booleans,
-- there are only two propositions, `True` and `False`,
-- and all true propositions are equal:

true_is_true  :  Bool
true_is_true  =  two_is_even == four_is_even

-- So Fermat's Last Theorem and 1 + 1 = 2 have the same value.

-- This seems fishy.

-- A different perspective is that:
-- * each logical proposition is distinct and
-- * a proof of a proposition is a conceptual object in its own right.


{-  Propositions as Types  -}

-- the evenness predicate on natural numbers as an Nat-indexed type:
public export
data  Even : Nat -> Type  where
	-- zero is even:
	Z_even  :  Even Z
	-- double successor preserves evenness:
	SS_even  :  Even n -> Even (S (S n))

{-
                                                                    
                                          SS_even                   
                      SS_even            (SS_even                   
   Z_even              Z_even              Z_even)     :  Even n    
   ---       ---       ---       ---       ---                      
    0         1         2         3         4   ...    :  (n : Nat) 
                                                                    
 -}

-- We can construct elements of type `Even n` only when `n` is even.
-- Moreover, each type `Even (2 * m)` contains exactly one element.

two_even  :  Even 2
two_even  =  SS_even Z_even

four_even  :  Even 4
four_even  =  SS_even two_even

-- We can think of an *element of a type* as a *proof of a proposition*
-- and we can manipulate these proofs in our programs
-- just like any other data.
-- 
-- * An *expression* of type `Even n`
--   acts as a *proof* that `n` is even.
-- 
-- * A *context variable* of type `Even n`
--   acts as an *assumption* that `n` is even.
-- 
-- * We can use pattern matching to examine the possible
--   reasons that an assumption could be true.
-- 
-- * Because the type `Even n` is indexed by the type `Nat`,
--   case splitting an assumption of type `Even n`
--   gives us information about the Nat `n` as well.

-- The constructor `SS_even` says that the double-successor
-- of an even number is even.
-- We can prove the converse as well:
public export
pp_even  :  Even (S (S n)) -> Even n
pp_even (SS_even n_even)  =  n_even


{-  Proof Validity and Totality  -}

-- Only a *total expression* of a type corresponds to
-- a *valid proof* of the corresponding proposition:

partial
everything_even  :  (n : Nat) -> Even n
everything_even n  =  pp_even (everything_even (S (S n)))

-- We can insist on totality using the directicve `%default total`

-- The sum of two even numbers is even:

public export
even_plus_even  :  Even m -> Even n -> Even (m + n)
even_plus_even {m = 0} Z_even n_even  =  n_even
even_plus_even {m = S (S m)} (SS_even m_even) n_even  =
	let
		IH  =  even_plus_even m_even n_even
	in
		SS_even IH

-- On proof strategy:
-- * An *inductive proof* is just a *recursive function`*.
-- 
-- * Addition is defined by recursion on its first argument
--   so we try proof by induction on the assumption
--   corresponding to the first summand.

-- On variable names:
-- * The assumption `Even m` is indexed by the the Nat `m`.
--   We can *explicitly bind* an implicit argument to name it.
--   This is helpful when Idris would choose a bad variable name.

even_times_even'  :  Even m -> Even n -> Even (m * n)
even_times_even' {m = 0} Z_even {n = n} n_even  =  Z_even
even_times_even' {m = S (S m)} (SS_even m_even) {n = n} n_even  =
	even_plus_even {m = n} {n = n + m * n} n_even $
	even_plus_even {m = n} {n = m * n} n_even $
	even_times_even' {m = m} {n = n} m_even n_even

-- On proof engineering:
-- * During the development of a proof sometimes we need to provide
--   implicit arguments explicitly to communicate what we want to do
--   so that Idris is able to compute the types of the goals. 
-- * After the proof is finished we may choose to delete them
--   if they can be inferred from the explicit arguments.

public export
even_times_even  :  Even m -> Even n -> Even (m * n)
even_times_even Z_even n_even  =  Z_even
even_times_even (SS_even m_even) n_even  =
	even_plus_even n_even $
	even_plus_even n_even $
	even_times_even m_even n_even


{-  Relations as Boolean-Valued Functions  -}

-- A *relation* is a predicate about multiple things.

-- The `Nat` insatance of the `( <= )` method:
is_lte  :  Nat -> Nat -> Bool
is_lte 0 n  =  True
is_lte (S m) 0  =  False
is_lte (S m) (S n)  =  is_lte m n

three_is_lte_five  :  Bool
three_is_lte_five  =  3 `is_lte` 5

four_is_lte_six  :  Bool
four_is_lte_six  =  4 `is_lte` 6


{-  Relations as Indexed Types  -}

-- ( ≤ ) as a type indexed by two `Nat`s (from Data.Nat):
data  LTE'  :  Nat -> Nat -> Type  where
	-- zero comes first:
	LTEZero'  :  LTE' Z n
	-- successor preserves order:
	LTESucc'  :  LTE' m n -> LTE' (S m) (S n)

{-
  \ n   0               1               2               3    ...
  m /-----------------------------------------------------------
    |
  0 |  ≤Z              ≤Z              ≤Z              ≤Z
    |
  1 |                ≤S ≤Z           ≤S ≤Z           ≤S ≤Z
    |
  2 |                              ≤S (≤S ≤Z)      ≤S (≤S ≤Z)
    |
  3 |                                            ≤S (≤S (≤S ≤Z))
  . |
  . |
  . |
 -}

-- For any `m , n : Nat`, the type `LTE m n` contains:
--
-- * exactly one element if m ≤ n,
-- * and no elements otherwise. (we'll see this in two weeks)

-- The indexed type family `LTE` axiomatizes
-- the less than or equal to relation

-- An element of type `LTE m n`
-- represents a proof that m ≤ n.

two_lte_three  :  LTE 2 3
two_lte_three  =  LTESucc (LTESucc LTEZero)

three_lte_four  :  LTE 3 4
three_lte_four  =  LTESucc two_lte_three

four_lte_three  :  LTE 4 3
four_lte_three  =  LTESucc $ LTESucc $ LTESucc ?stuck


{-  Some LTE Properties  -}

-- The constructor `LTESucc` says that if m ≤ n then S m ≤ S n.
-- We can prove the converse as well:
public export
lte_pred  :  LTE (S m) (S n) -> LTE m n
lte_pred (LTESucc m_lte_n)  =  m_lte_n

-- LTE is a reflexive relation:
public export
lte_refl  :  {n : Nat} -> LTE n n
lte_refl {n = 0}  =  LTEZero
lte_refl {n = S n}  =
	let
		IH = lte_refl {n = n}
	in
		LTESucc IH

-- LTE is a transitive relation:
-- (note that Idris lets you reorder the implicit arguments)
public export
lte_trans  :  LTE l m -> LTE m n -> LTE l n
lte_trans {l = 0} LTEZero {m = m} m_lte_n {n = n}  =  LTEZero
lte_trans {l=S l} (LTESucc l_lte_m) {m=S m} (LTESucc m_lte_n) {n=S n}  =
	LTESucc (lte_trans l_lte_m {m = m} m_lte_n)

