{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 8, 2023-03-20
 -- 
 -- Algebraic Interfaces
 --}

module Lecture8

import Data.String

-- An interface is called *algebraic*
-- if it is meant to specify a set of equations
-- that its instances should satisfy.


{-- Algebraic Interfaces for Types --}

-- Indeed, we already know some algebraic interfaces:

namespace  Eq
	interface  Eq' (a : Type)  where
		(==)  :  a -> a -> Bool
		x == y  =  not (x /= y)
		--
		(/=)  :  a -> a -> Bool
		x /= y  =  not (x == y)
		-- laws:
		-- refl  :  (x : a) -> x == x
		-- symm  :  (x , y : a) -> x == y -> y == x
		-- tran  :  (x , y , z : a) -> x == y -> y == z -> x == z


data  RoShamBo : Type  where
	Rock , Paper , Scissors  :  RoShamBo

-- bad equality:
implementation  Eq RoShamBo  where
	Rock == Paper  =  True
	Paper == Scissors  =  True
	Scissors == Rock  =  True
	_ == _  =  False



-- types with a combining operation:
namespace  Semigroup
	interface  Semigroup' (a : Type)  where
		(<+>)  :  a -> a -> a
		-- laws:
		-- assoc  :  (x , y , z : a) -> (x <+> y) <+> z == x <+> (y <+> z)


implementation  Semigroup Nat  where
	(<+>)   =  (+)

-- :doc Semigroup to see instances


-- semigroups with a neutral element:
namespace  Monoid
	interface  Semigroup a => Monoid' (a : Type)  where
		neutral  :  a
		-- laws:
		-- unit_l  :  (x : a) -> neutral <+> x == x
		-- unit_r  :  (x : a) -> x <+> neutral == x

implementation  Monoid Nat  where
	neutral  =  0

-- :doc Monoid to see instances


-- we can combine a whole list of monoid elements:
combine  :  Monoid m => List m -> m
combine []  =  neutral
combine (x :: xs)  =  x <+> (combine xs)




{-- Algebraic Interfaces for Type Constructors --}

-- a computation that returns a numberic type:
getInt  :  IO Integer
getInt  =  do
	putStr "number: "
	s <- getLine
	pure $
	case parsePositive s of
		Nothing => 0
		Just n => n

-- to avoid implicit binding of `id`:
Idty  :  a -> a
Idty  =  \x => x

-- forward composition:
Comp  :  (a -> b) -> (b -> c) -> (a -> c)
Comp f g  =  \x => g (f x)



-- type constructors that support mapping:
namespace  Functor
	interface  Functor' (t : Type -> Type)  where
		map  :   (a -> b) -> t a -> t b
		-- laws:
		-- map_idty  :  map Idty == Idty
		-- map_comp  :  map (Comp f g) == Comp (map f) (map g)


-- :doc Functor to see instances

implementation  [MaybeFunctor] Functor Maybe  where
	map f Nothing  =  Nothing
	map f (Just x)  =  Just (f x)



-- update the element at the specified index of a list:
update  :  (new : a) -> (i : Nat) -> List a -> Maybe (List a)
update new i []  =  Nothing
update new 0 (x :: xs)  =  Just (new :: xs)
update new (S i) (x :: xs) with (update new i xs)
	_ | Nothing  =  Nothing
	_ | Just new_tail  =  Just (x :: new_tail)


-- using mapping:
update'  :  (new : a) -> (i : Nat) -> List a -> Maybe (List a)
update' new i []  =  Nothing
update' new 0 (x :: xs)  =  Just (new :: xs)
update' new (S i) (x :: xs)  =  map (x :: ) (update' new i xs)


-- functors that respect functions:
namespace  Applicative
	interface  Functor t => Applicative' (t : Type -> Type)  where
		pure  :  a -> t a
		(<*>) :  t (a -> b) -> t a -> t b
		-- plus laws


-- :doc Applicative to see instances

implementation  [MaybeApplicative] Applicative Maybe  where
	pure x  =  Just x
	--
	(Just f) <*> (Just x)  =  Just (f x)
	(Just f) <*> Nothing  =  Nothing
	Nothing <*> (Just x)  =  Nothing
	Nothing <*> Nothing  =  Nothing

-- applicative functors let you map functions of higher arity:
map2  :  Applicative t => (a -> b -> c) -> t a -> t b -> t c
map2 f x y  =  pure f <*> x <*> y
{-
	f  :  a -> b -> c
	pure f  :  t (a -> b -> c)
	(pure f <*> )  :  t a -> t (b -> c)
	pure f <*> x  :  t (b -> c)
	(pure f <*> x <*> )  :  t b -> t c
	pure f <*> x <*> y  :  t c
 -}

plusM  :  Num a => Maybe a -> Maybe a -> Maybe a
plusM  =  map2 (+)

plusL  :  Num a => List a -> List a -> List a
plusL  =  map2 (+)


namespace  Monad
	interface  Applicative t => Monad' (t : Type -> Type)  where
		(>>=)  :  t a -> (a -> t b) -> t b
		tx >>= f  =  join $ map f tx
		--
		join  :  t (t a) -> t a
		join ttx  =  ttx >>= id
		-- plus laws

-- :doc Monad to see instances

implementation [MaybeMonad] Monad Maybe  where
	join Nothing  =  Nothing
	join (Just Nothing)  =  Nothing
	join (Just (Just x))  =  Just x



-- Because do-notation desugars to `(>>=)`
-- we can use it for any monad.
plusMnd  :  Monad m => Num a => m a -> m a -> m a
plusMnd mx my  =  do
	x <- mx
	y <- my
	pure (x + y)


-- which desugars to:
plusMnd'  :  Monad m => Num a => m a -> m a -> m a
plusMnd' mx my  =  mx >>= \ x => my >>= \ y => pure (x + y)

