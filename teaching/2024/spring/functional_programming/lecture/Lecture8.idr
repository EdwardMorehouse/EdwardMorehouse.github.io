{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 8 (2024-04-01)
 -- 
 -- Algebraic Interfaces
 --}


module Lecture8

-- An interface is called *algebraic* if it is meant to specify
-- a set of equations that its instances must satisfy.


{-- Algebraic Interfaces for Types --}

-- Indeed, we already know some algebraic interfaces.


-- Types with an equivalence relation:
infix 6 ==~
interface  Eq' (a : Type)  where
	(==~)  :  a -> a -> Bool
	-- ...
	-- laws:
	--refl  :  {x : a} -> x ==~ x
	--symm  :  {x , y : a} -> x ==~ y -> y ==~ x
	--tran  :  {x , y , z : a} -> x ==~ y -> y ==~ z -> x ==~ z

-- from homework 1:
data  Roshambo : Type  where
	Rock , Paper , Scissors  :  Roshambo

-- bad equality:
implementation  Eq Roshambo  where
	Rock == Paper  =  True
	Paper == Scissors  =  True
	Scissors == Rock  =  True
	_ == _  =  False


-- Types with an associative combining operation:
infixl 8 <+>~
interface  Semigroup' (a : Type)  where
	(<+>~)  :  a -> a -> a
	-- law:
	--assoc  :  {x , y , z : a} -> (x <+>~ y) <+>~ z == x <+>~ (y <+>~ z)

-- :doc Semigroup to see instances

implementation  Semigroup Nat  where
	--x <+> y = y  -- okay as a semigroup but will not be a monoid
	(<+>)  =  (+)

-- Semigroups with a neutral element:
interface  Semigroup a => Monoid' (a : Type)  where
	neutral'  :  a
	-- laws:
	--unit_l  :  {x : a} -> neutral' <+> x == x
	--unit_r  :  {x : a} ->  x <+> neutral' == x

-- :doc Monoid to see instances

-- Fact: a semigroup can have at most one neutral element.

implementation  Monoid Nat  where
	neutral  =  Z

-- We can combine a whole list of monoid elements:
combine  :  Monoid a => List a -> a
combine []  =  neutral
combine (x :: xs)  =  x <+> (combine xs)


{-- Algebraic Interfaces for Type Constructors --}

Idty  :  a -> a
Idty  =  id

-- Type constructors that support mapping:
interface  Functor' (t : Type -> Type)  where
	map'  :  (a -> b) -> t a -> t b
	-- laws:
	--map_idty  :  {x : t a} -> map' Idty x == Idty x
	--map_comp  :  {x : t a} -> map' (g . f) x ==  (map g . map f) x

-- :doc Functor to see instances

-- `Maybe` is a functor: (from lab 4)
implementation  Functor' Maybe  where
	map' f Nothing  =  Nothing
	map' f (Just x)  =  Just (f x)

-- replace the element at the specified index of a list:
update  :  (new : a) -> (i : Nat) -> List a -> Maybe (List a)
update new i []  =  Nothing
update new Z (x :: xs)  =  Just (new :: xs)
update new (S i) (x :: xs)  =  case update new i xs of
	Nothing => Nothing
	Just ys => Just (x :: ys) -- Just ((x :: ) ys)

-- using the fact that `Maybe` is a functor:
update'  :  (new : a) -> (i : Nat) -> List a -> Maybe (List a)
update' new i []  =  Nothing
update' new Z (x :: xs)  =  Just (new :: xs)
update' new (S i) (x :: xs)  =  map (x :: ) (update' new i xs)


-- Functors that respect functions:
infixl 3 <*>~
interface  Functor t => Applicative' (t : Type -> Type)  where
	pure'  :  a -> t a
	(<*>~) :  t (a -> b) -> t a -> t b
	-- plus laws

-- :doc Applicative to see instances

-- `Maybe` is an applicative functor:
implementation  Applicative' Maybe  where
	pure'  =  Just
	Just f <*>~ Just x  =  Just (f x)
	_ <*>~ _  =  Nothing

-- Applicative functors let you map functions of higher arity:
map2  :  Applicative t => (a -> b -> c) -> t a -> t b -> t c
map2 f x y  =  pure f <*> x <*> y

{- typing derivation:
	f  :  a -> b -> c
	pure f  :  t (a -> b -> c)
	(pure f <*> )  :  t a -> t (b -> c)
	pure f <*> x  :  t (b -> c)
	(pure f <*> x <*> )  :  t b -> t c
	pure f <*> x <*> y  :  t c
 -}

infixl 8 +?
(+?)  :  Num a => Maybe a -> Maybe a -> Maybe a
(+?)  =  map2 (+)


-- Applicative functors that combine with themselves:
infixl 1 >>=~
interface  Applicative t => Monad' (t : Type -> Type)  where
	(>>=~)  :  t a -> (a -> t b) -> t b
	x >>=~ f  =  (join' . map f) x
	-- or
	join'  :  t (t a) -> t a
	join'  =  ( >>=~ id)
	-- plus laws

-- :doc Monad to see instances

-- `Maybe` is an applicative functor:
implementation  Monad' Maybe  where
	join' Nothing  =  Nothing
	--join' (Just z)  =  z
	join' (Just Nothing)  =  Nothing
	join' (Just (Just x))  =  Just x


-- Because do-notation desugars to `(>>=)`
-- we can use it for any monad, not only `IO`.

