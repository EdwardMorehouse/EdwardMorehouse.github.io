{-
 - Interlude.hs
 -
 - non-standard haskell interlude
 -
 - edward morehouse
 - emorehouse@wesleyan.edu
 -}


{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
--{-# LANGUAGE TypeOperators #-}


module Interlude where

import Prelude hiding (id)
import Control.Applicative
import Control.Monad
import Control.Category
import Control.Arrow 


{- composition -}

(⋅)  ∷  ∀ a b c (hom ∷ * → * → *) . Category hom ⇒
	hom a b → hom b c → hom a c
(⋅)  =  (>>>)
infixl 2 ⋅

(∘)  ∷  ∀ a b c (hom ∷ * → * → *) . Category hom ⇒
	hom b c → hom a b → hom a c
(∘)  =  (<<<)
infixr 2 ∘


{- unit -}

type Top  =  ()

unit  ∷  Top
unit  =  ()

(!)  ∷  ∀ a (hom ∷ * → * → *) . Arrow hom ⇒
	hom a Top
(!)  =  arr (const unit)


{- product -}

type Product  =  (,)
--type a × b  =  (a , b)

--data a + b  =  LLeft a | RRight b

(⊗)  ∷  ∀ a₁ a₂ b₁ b₂ (hom ∷ * → * → *) . Arrow hom ⇒
	hom a₁ b₁ → hom a₂ b₂ → hom (Product a₁ a₂) (Product b₁ b₂)
(⊗)  =  (***)

tuple  ∷  ∀ a b c (hom ∷ * → * → *) . Arrow hom ⇒
	hom c a → hom c b → hom c (Product a b)
tuple  =  (&&&)

(∆)  ∷  ∀ a (hom ∷ * → * → *) . Arrow hom ⇒
	hom a (Product a a)
(∆)  =  tuple id id

untuple  ∷  ∀ a b c (hom ∷ * → * → *) . Arrow hom ⇒
	hom c (Product a b) → (hom c a , hom c b)
untuple h  =  (h ⋅ arr fst , h ⋅ arr snd)


{- empty -}

data Bot where

(¡)  ∷  ∀ a (hom ∷ * → * → *) . Arrow hom ⇒
	hom Bot a
(¡)  =  arr (\ x -> error "congratulations, you found an element of the empty type")


{- coproduct -}

type Coproduct  =  Either

(⊕)  ∷  ∀ a₁ a₂ b₁ b₂ (hom ∷ * → * → *) . ArrowChoice hom ⇒
	hom a₁ b₁ → hom a₂ b₂ → hom (Coproduct a₁ a₂) (Coproduct b₁ b₂)
(⊕)  =  (+++)

cotuple  ∷  ∀ a b c (hom ∷ * → * → *) . ArrowChoice hom ⇒
	hom a c → hom b c → hom (Coproduct a b) c
cotuple  =  (|||)

(∇)  ∷  ∀ a (hom ∷ * → * → *) . ArrowChoice hom  ⇒
	hom (Coproduct a a) a
(∇)  =  cotuple id id

uncotuple  ∷  ∀ a b c (hom ∷ * → * → *) . ArrowChoice hom ⇒
	hom (Coproduct a b) c → (hom a c , hom b c)
uncotuple h  =  (arr Left ⋅ h , arr Right ⋅ h)



{-
 - type synonyms and shortcuts:
 -}

{- for total orders -}

(≤)  =  (<=)
infix 4 ≤

(≥)  =  (>=)
infix 4 ≥


{- for equality types -}

(≠)  =  (/=)
infix 4 ≠


{- for booleans -}

(∧)  =  (&&)
infixr 3 ∧

(∨)  =  (||)
infixr 2 ∨



{- for lists -}

type List = []

nil ∷ ∀ a . List a
nil  =  []

cons ∷ ∀ a . a → List a → List a
cons = (:)

(∈) ∷ ∀ a . Eq a ⇒ a → List a → Bool
(∈) = elem






{- for natural numbers -}

nats  =  [0 ..]




{-
-- not satisfied with this
(⋅⊃)  ∷  ∀ a b c d . (a → b → c) → (c → d) → a → b → d
f ⋅⊃ g  =  f ⋅ (⋅ g)
infixl 9 ⋅⊃

{- for application -}

-- totally unnecessary: get rid of
apply  ∷  ∀ a b . (a → b) → a → b
apply  =  \ f x -> f x
 -}


{-
 - useful functions:
 -}

{- get the graph of a function on a list of arguments -}
graph_on  ∷  ∀ a b
	. (a → b)                                  -- a function
	→ List a                                   -- an argument list
	→ List (Product a b)                       -- the resulting graph
graph_on f  =  map (tuple id f)


{- least element satisfying a predicate -}
-- found it! this is "until" in the stdlib
least  ∷  ∀ a
	. (a → Bool)                   -- a predicate
	→ (a → a)                      -- a step function
	→ a                            -- a starting point
	→ a                            -- the first generated element satisfying the predicate
least predicate next first
	| predicate first  =  first
	| otherwise  =  least predicate next (next first)

-- this must be somewhere in the prelude...
times  ∷  ∀ a (hom ∷ * → * → *) . Category hom ⇒
	Integer → hom a a → hom a a
n `times` f
	| n < 0  =  error "can't iterate a function fewer than zero times"
	| n == 0  =  id
	| otherwise  =  f ⋅ ((n - 1) `times` f)


{-
 - stuff for monads:
 -}

{-
 - i can't really think in terms of >>=
 - so to make a monad instance
 - i just define the natural transfomation μ
 - or the kleisli composition komp
 - and define (>>=) in terms of one of them
 -}

join_to_bind  ∷  ∀ (m ∷ * → *)
	. Functor m                                          -- for any monadic functor
	⇒ (∀ t . (m (m t) → m t))                            -- the join operator of the monad
	→ (∀ a b . (m a → (a → m b) → m b))                  -- the resulting bind operator
join_to_bind mu m_x f  =  (fmap f ⋅ mu) m_x

komp_to_bind  ∷  ∀ (m ∷ * → *)
	. Functor m                                          -- for any monadic functor
	⇒ (∀ a b c . (a → m b) → (b → m c) → (a → m c))      -- the kleisli composition of the monad
	→ (∀ a b . (m a → (a → m b) → m b))                  -- the resulting bind operator
komp_to_bind komp m_x f  =  (id `komp` f) m_x
-- komp_to_bind komp m_x f  =  (fmap f `komp` id) m_x

{- 
 --not needed since join and komp are derived by monad

bind_to_join  ∷  ∀ (m ∷ * → *)
	. Functor m                                          -- for any monadic functor
	⇒ (∀ a b . m a → (a → m b) → m b)                    -- the bind operator of the monad
	→ (∀ t . (m (m t) → m t))                            -- the resulting join operator
bind_to_join bind mm_x  =  mm_x `bind` id

bind_to_komp  ∷  ∀ (m ∷ * → *)
	. Functor m                                          -- for any monadic functor
	⇒ (∀ a b . m a → (a → m b) → m b)                    -- the bind operator of the monad
	→ (∀ a b c . (a → m b) → (b → m c) → (a → m c))      -- the resulting kleisli composition
bind_to_komp bind f g x  =  f x `bind` g

join_to_komp  ∷  ∀ (m ∷ * → *)
	. Functor m                                          -- for any monadic functor
	⇒ (∀ t . (m (m t) → m t))                            -- the join operator of the monad
	→ (∀ a b c . (a → m b) → (b → m c) → (a → m c))      -- the resulting kleisli composition
join_to_komp mu f g  =  f ⋅ fmap g ⋅ mu

komp_to_join  ∷  ∀ (m ∷ * → *)
	. Functor m                                          -- for any monadic functor
	⇒ (∀ a b c . (a → m b) → (b → m c) → (a → m c))      -- the kleisli composition of the monad
	→ (∀ t . (m (m t) → m t))                            -- the resulting join operator
komp_to_join komp mm_x  =  (id `komp` id) mm_x

 -}

