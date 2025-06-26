{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 11 (2024-04-22)
 -- 
 -- Inductive Equality
 --}


module Lecture11

import Data.Vect
import Syntax.PreorderReasoning

%default total  --  to ensure proof validity


{-  Equality as a Boolean-Valued Function  -}

-- equality relation for natural numbers in propositions-as-booleans:
is_equal  :  Nat -> Nat -> Bool
is_equal 0 0  =  True
is_equal (S m) (S n)  =  is_equal m n
is_equal _ _  =  False


{-  Equality as an Indexed Type  -}

-- equality relation for natural numbers in propositions-as-types:
data  EqualNat : Nat -> Nat -> Type  where
	Zequal  :  EqualNat Z Z
	Sequal  :  EqualNat m n -> EqualNat (S m) (S n)

two_is_two  :  EqualNat 2 2
two_is_two  =  Sequal $ Sequal Zequal

-- We can define such an equality type for any inductively defined type.
-- But remarkably, we can define a single indexed type family
-- for the equality relation on *any* type:

data  Equal' : a -> b -> Type  where
	-- everything is equal to itself:
	Refl'  :  Equal' x x


-- Idris has `Equal` in the standard library with syntactic sugar `(=)`.

-- The only way to construct a term of type `Equal x y` is if 
-- the terms `(x : a)` and `(y : b)` are *computationally the same*.
-- This requires the types `a` and `b` also be computationally the same.

four_is_four  :  2 + 2 = 2 * 2
four_is_four  =  Refl

-- adding a zero on the left:
public export
plus_zero_left  :  {n : Nat} -> 0 + n = n
plus_zero_left  =  Refl

-- adding a successor on the left:
public export
plus_succ_left  :  {m , n : Nat} -> (S m) + n = S (m + n)
plus_succ_left  =  Refl


{--  On Dependent Pattern Matching  --}

-- An expression of type `Equal x y` acts as
-- a proof that `x` and `y` are equal.

-- A context variable of type `Equal x y` acts as
-- an assumption that `x` and `y` are equal.

-- The only element constructor `Refl` has type `Equal x x`,
-- so case analysis of an assumption of type `Equal x y`
-- triggers the discovery that `x` and `y` must be the same.

	-- adding a zero on the right (naive version):
plus_zero_right'  :  {m : Nat} -> m + 0 = m
plus_zero_right' {m = 0}  =  Refl
plus_zero_right' {m = S m}  =
	let
		IH = plus_zero_right' {m = m}
	in
		succ_equal IH
	where
		succ_equal  :  i = j -> S i = S j
		succ_equal {i = k} Refl {j = k}  =  Refl

-- This `succ_equal` function is pretty nice, but the proof didn't
-- depend on the type being `Nat` or the function being `S`.

-- In fact, *every* function preserves equality.

public export
congruence  :  (0 f : a -> b) -> (path : x = y) -> f x = f y
congruence f Refl  =  Refl

-- `congruence` in the standard library, called `cong`.

-- adding a zero on the right (streamlined version using cong):
public export
plus_zero_right  :  {m : Nat} -> m + 0 = m
plus_zero_right {m = 0}  =  Refl
plus_zero_right {m = S m}  =  cong S plus_zero_right

-- adding a successor on the right:
public export
plus_succ_right  :  {m , n : Nat} -> m + (S n) = S (m + n)
plus_succ_right {m = 0}  =  Refl
plus_succ_right {m = S m}  =  cong S plus_succ_right

-- There's a fair amount of computation happening here
-- and it can sometimes be hard to remember what's going on.
-- That may be fine for Idris, but it's not great for humans.

-- Let's establish some basic facts about equality
-- so that we can reason at a higher level of abstraction.

-- In week 8 we said that equality should be an *equivalence relation*.

-- Equality is a symmetric relation:
symmetry  :  x = y -> y = x
symmetry Refl  =  Refl

-- `symmetry` is in the standard library, called `sym`.

-- Equality is a transitive relation:
transitivity  :  from = via -> via = to -> from = to
transitivity Refl  =  id

-- `transitivity` is in the standard library, called `trans`.

-- The `Equal` indexed type family that we have defined
-- axiomatizes an equivalence relation on any type!

-- We can use transitivity to write equality proofs
-- using *algebra* rather than *computation*.

-- addition is commutative (using transitivity):
plus_comm'  :  {m , n : Nat} -> m + n = n + m
plus_comm' {m = 0}  =  transitivity
	{from = 0 + n}       plus_zero_left
	{via = n}            (sym plus_zero_right)
	{to = n + 0}
plus_comm' {m = S m}  =  transitivity
	{from = S m + n}       plus_succ_left
	{via = S (m + n)}      $ transitivity (cong S plus_comm')
	{via = S (n + m)}      (sym plus_succ_right)
	{to = n + S m}

-- This is okay but the notation is not very friendly.
-- By importing the module `Syntax.PreorderReasoning`
-- we can write chains of equalities in a more readable way.

-- addition is commutative (using equational reasoning):
public export
plus_comm  :  {m , n : Nat} -> m + n = n + m
plus_comm  {m = 0}  =  Calc $
	|~ 0 + n
	~~ n            ...(plus_zero_left)
	~~ n + 0        ...(sym plus_zero_right)
plus_comm  {m = S m}  =  Calc $
	|~ S m + n
	~~ S (m + n)    ...(plus_succ_left)
	~~ S (n + m)    ...(cong S plus_comm)
	~~ n + S m      ...(sym plus_succ_right)

-- addition is associative (by induction on m):
public export
plus_assoc  :  {l , m , n : Nat} -> l + (m + n) = (l + m) + n
plus_assoc {m = 0}  =  Calc $
	|~ l + (0 + n)
	~~ l + n             ...(cong (l + ) plus_zero_left)
	~~ (l + 0) + n       ...(cong ( + n) $ sym plus_zero_right)
plus_assoc {m = S m}  =  Calc $
	|~ l + (S m + n)
	~~ l + S (m + n)     ...(cong (l + ) plus_succ_left)
	~~ S (l + (m + n))   ...(plus_succ_right)
	~~ S ((l + m) + n)   ...(cong S plus_assoc)
	~~ S (l + m) + n     ...(sym plus_succ_left)
	~~ (l + S m) + n     ...(cong ( + n) $ sym plus_succ_right)


{--  Equality of Types  --}

-- An indexed type family is a function from the indexing type to `Type`.
-- So we can use conguence to turn an equality between indices
-- into an equality between types.

vect_length_sym  :  {m , n : Nat} -> Vect (m + n) a = Vect (n + m) a
vect_length_sym  =  cong (\ len => Vect len a) plus_comm

-- If we know that two types are equal
-- then we can write a coercion function between them:
public export
coerce  :  {0 a , b : Type} -> (path : a = b) -> a -> b
coerce Refl  =  id

-- twisted Vect concatenation (using coerce):
twist_concat'  :  {m , n : Nat} -> Vect m a -> Vect n a -> Vect (n + m) a
twist_concat' xs ys  =  coerce vect_length_sym (xs ++ ys)

-- This is a common pattern.
-- Idea:
-- * by congruence:
--   if the indices are equal then the indexed types are equal.
-- * by coercion:
--   if the indexed types are equal then there's a function between them.
--
-- Combining these is called "transport":

public export
transport  :  {0 a : Type} -> (0 fam : a -> Type) ->
	{0 x , y : a} -> (path : x = y) ->
	fam x -> fam y
transport fam Refl  =  id

{-
             fam x                                   fam y             
           _________                               _________           
          /         \                             /         \          
         /     p     \     transport fam path    / transport \         
        |             |   ------------------->  |   fam path  |        
         \           /                           \     p     /         
          \_________/                             \_________/          
                                   path                                
               x    ===============================    y         : a   
                                                                       
 -}

-- Now we can write twisted vector concatenation as a one-liner.

-- twisted Vect concatenation (using transport):
twist_concat  :  {m , n : Nat} -> Vect m a -> Vect n a -> Vect (n + m) a
twist_concat xs ys  =  transport (\ n => Vect n a) plus_comm (xs ++ ys)

{-
        Vect (m + n) a                          Vect (n + m) a         
           _________                               _________           
          /         \     transport (Vect _ a)    /         \          
         /           \         plus_comm         /           \         
        |  xs ++ ys   |   ------------------->  |             |        
         \           /                           \           /         
          \_________/                             \_________/          
                               plus_comm                               
             m + n  ===============================  n + m       : Nat 
                                                                       
 -}

-- `transport` is in the standard library, called `replace`.
-- Inconveniently, it takes the indexed type family
-- as an implicit argument called `p`.

-- Note: Idris has a construct called `rewrite` that can be used
-- for rewriting (some) equalities.
-- But it is not type directed and we will not use it in this course.
