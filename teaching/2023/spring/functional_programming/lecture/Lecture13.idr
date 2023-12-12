{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 13, 2023-04-24
 -- 
 -- Inductive Equality
 --}

-- TODO: announce lab sheet

module Lecture13    

-- We all know where this is going
-- But let's pretend we don't

{-
    A Practical Introduction to Equality in Idris
    by Michele De Pascalis
    (pron. Mikeele)
-}

import Data.Fin
import Data.Vect
import Syntax.PreorderReasoning

%default total

{- ACT 1: It goes in the square hole... ? -}

v5 : Vect 5 (Fin 5)
v5 = range  -- [0, 1, 2, 3, 4]

v0_5 : Vect (0 + 5) (Fin 5)
v0_5 = v5 -- Does `v5` fit here?

v5_0 : Vect (5 + 0) (Fin 5)
v5_0 = v5 -- Does `v5` fit here?

-- Let's see something more abstract

forall_n_vect_0_n : (n : Nat) -> Vect (0 + n) (Fin n)
forall_n_vect_0_n n = v  -- Does `v` fit here?
    where
    v : Vect n (Fin n)
    v = range

forall_n_vect_n_0 : (n : Nat) -> Vect (n + 0) (Fin n)
forall_n_vect_n_0 n = ?g50 -- The bets are open
    where
    v : Vect n (Fin n)
    v = range

-- Houston, meil on probleem!

-- `0 + 5` <computes down to> `5`
-- `5 + 0` <computes down to> `5`

-- But when defining the dependent functions above,
-- our scope is abstract over `n`.
-- `0 + n` <computes down to> `n`, why?
-- Recall definition of `+`, it is recursive on the left.
-- What about `n + 0`?

-- Case splitting can get us somewhere, but only so far.
forall_n_vect_n_0_cs : (n : Nat) -> Vect (n + 0) (Fin n)
forall_n_vect_n_0_cs 0 = v
    where
    v : Vect 0 (Fin 0)
    v = range
forall_n_vect_n_0_cs (S 0) = v
    where
    v : Vect 1 (Fin 1)
    v = range
forall_n_vect_n_0_cs (S (S k)) = ?g_50 -- What now?
    where
    v : Vect (S (S k)) (Fin (S (S k)))
    v = range

-- Idris can "see" that terms that compute down to the same
-- term represent the same entity.
-- But sometimes we know that all instances of two terms
-- represent the same entity, even though in the context
-- there is not enough information to compute them down.

-- Excursus: decidability of equality.

{- ACT 2: Unbox Therapy -}

-- Refresher: the anatomy of an inductive family definition
data Vect' : Nat -> a -> Type where
--    |       |     └-- second index type
--    |       └-- first index type
--    └-- name of the family
    Nil' : Vect' 0 a
--   |           | └-- second index for the constructor
--   |           └-- first index for the constructor
--   └-- name of the constructor
    (::) : a -> Vect' n a -> Vect' (S n) a
--   |                | |            |   └-- second index for the constructor
--   |                | |            └-- first index for the constructor
--   |                | └-- second index for a recursive argument
--   |                └-- first index for a recursive argument
--   └-- name of the constructor

-- Note that the indices of the constructors are not "free".

-- Case splitting works accordingly.

double : Nat -> Nat
double 0 = 0
double (S k) = S (S (double k))

-- The goal changes

repeat : Vect n a -> Vect (double n) a
repeat [] = []
repeat (x :: xs) = x :: x :: repeat xs

-- The context changes

repeat_exp : (n : Nat) -> Vect n a -> Vect (double n) a
repeat_exp 0 [] = ?g106_0
repeat_exp (S len) (x :: xs) = ?g106_1

-- Some constructors are weeded out

tail : Vect (S n) a -> Vect n a
tail (x :: xs) = xs

-- The terms that we give as indices for the constructors
-- *constrain* each other.
-- This also happens with binary relations.

-- Recall: the (<=) relation as an inductive family
data (<=) : Nat -> Nat -> Type where
    LEZero : 0 <= n
    LESucc : m <= n -> S m <= S n

le_S : {n : Nat} -> n <= S n
le_S {n = 0} = LEZero
le_S {n = (S k)} = LESucc (le_S)

le_trans : m <= n -> n <= p -> m <= p
le_trans LEZero _ = LEZero
le_trans (LESucc mlen) (LESucc nlep) = LESucc (le_trans mlen nlep)

-- Notice how case splitting `mlen` constrains `n`.
succ_lb : (m, n : Nat) -> S m <= n -> m <= n
succ_lb m (S n) (LESucc x) = ?g131_0
-- succ_lb m (S n) (LESucc mlen) =
--     le_trans n_le_Sn (LESucc mlen)

-- You could say that terms of an instance of an indexed
-- inductive family carry information about the indices
-- that appear in their type.

-- e.g. a term `x : Fin n` carries the information that
-- `n` is not zero.
-- a term `mlen : m <=  n` carries the information that if `n`
-- is zero, then `m` must be zero.

le_zero : (m : Nat) -> m <= 0 -> ?I_dont_care_145
le_zero 0 LEZero = ?g146_0

-- When constructing a term belonging to an instance of these
-- families, we may think that we are implicitly boxing
-- this information. When case splitting, we unbox it.

-- Can we construct a type family whose terms carry the
-- information that the indices in their type are equal?

{- ACT 3: Wait, so they were equal all along? -}

-- The trick: Idris allows us to repeat variables across
-- indices.

data Equal' : a -> b -> Type where
    Refl' : Equal' x x  -- `x` is implicitly bound

-- Notation for `Equal x y` --> `x = y`

t5eq5 : 5 = 5
t5eq5 = Refl

-- Let us construct some members of instances of `Equal`.
plus_0_eq_comp : {n : Nat} -> 0 + n = n
plus_0_eq_comp = Refl  -- Inspect me

-- Now let's get out unboxing knives.
unbox_eq : (x, y : a) -> x = y -> ?some_goal x y
unbox_eq x' x' Refl = ?unbox_eq_rhs_0  -- Inspect me after splitting

-- PROPERTIES

reflexivity : {x : a} -> x = x
reflexivity = Refl

symmetry: {x, y : a} -> x = y -> y = x
symmetry Refl = Refl

-- double induction
transitivity: {x, y, z : a} -> x = y -> y = z -> x = z
transitivity {x = x'} {y = x'} {z = x'} Refl Refl = Refl

-- Another way to define it: single induction
transitivity' : {x, y, z : a} -> x = y -> y = z -> x = z
transitivity' {x = x'} {y = x'} {z = z} Refl q = q

-- Function application preserves equality
cong' : {x, y : a} -> (f : a -> b) -> x = y -> f x = f y
cong' f Refl = Refl
-- Does your favourite programming language also have
-- congruence?

-- Remember that thing that we wanted to convince Idris of?
plus_0_eq : {n : Nat} -> n = n + 0
plus_0_eq {n = 0} = Refl
plus_0_eq {n = (S n')} = let
    IHn' = plus_0_eq {n = n'}
    in cong S IHn'

-- Bonus: using the induction principle for Nat
indNat : {p : Nat -> Type} -> (base : p 0) -> (step : {k : Nat} -> p k -> p (S k))
    -> (n : Nat) -> p n
indNat base step 0 = base
indNat base step (S m) = let
    ih = indNat {p} base step m
    in step ih

plus_0_eq' : (n : Nat) -> n = n + 0
plus_0_eq' = indNat Refl (cong S)

{- ACT 4: Would you like some sugar with that? -}

-- We will need this lemma:
plus_S : (m, n : Nat) -> S (m + n) = m + (S n)
plus_S 0 n = Refl
plus_S (S m) n = 
    let
        IHm = plus_S m n
    in cong S IHm
-- plus_S 0 n = Refl
-- plus_S (S m) n = 
--     let
--         IHm = plus_S m n
--     in cong S IHm

plus_comm : (m, n : Nat) -> m + n = n + m
plus_comm 0 n = plus_0_eq
plus_comm (S m) n = 
    let
        IHm = plus_comm m n
    in Calc $
        |~ S (m + n)
        ~~ S (n + m) ...( cong S IHm )
        ~~ n + S m   ...( plus_S n m )
-- We want to prove S (m + n) = n + S m.
-- IHm : m + n = n + m
-- So we get:
{-
    S (m + n)  
    S (n + m)  = (by congruence on IHm)
    n + S m.   = (by the lemma above)
-}
-- This reasoning can be formalized as an instance of transitivity:
-- `in transitivity (cong S IHm) (plus_S n m)`.
-- But it's not very readable.
-- In Idris 2, there is syntactic sugar for this kind of reasoning.
-- The syntax is as follows:
{- 
    Calc $
        |~ T0
        ~~ T1 ...( <reason for T0 = T1>   )
        ~~ T2 ...( <reason for T1 = T2>   )
        -- etc.
        ~~ TN ...( <reason for TN-1 = TN> )
-}
-- The above will have type `T0 = TN`.

-- Alright, that's all folks, see you all in the lab on Friday!
-- ...
-- .....
-- "But you still did not show us how to give a `Vect n a` for a `Vect (n + 0) a`!"
-- Right, erm...
-- ♬ Roundabout starts playing ♬
--                                                                         ██▒▒            
--                                                   ▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒  ██▒▒        
--                                                   ▒▒   To Be Continued      ██▒▒      
--                                                   ██████████████████████░░██░░          
--                                                                         ██░░            
