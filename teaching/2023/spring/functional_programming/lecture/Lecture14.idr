{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 14, 2023-05-01
 -- 
 -- Equality for Types
 --}

 module Lecture14

import Data.Fin
import Data.Vect
import Syntax.PreorderReasoning

%default total

-- Before starting, review non trivial computation in
-- preorder reasoning goals

plus_S : (m, n : Nat) -> (S m) + n = m + S n
plus_S m n = Calc $
    |~ S m + n
    ~~ m + S n  ...( ?inspect_me )

-- So, back to the matter at hand

forall_n_vect_n_0 : (n : Nat) -> Vect (n + 0) (Fin n)
forall_n_vect_n_0 n = ?oh_no_not_you_again
    where
    v : Vect n (Fin n)
    v = range

-- We know that `Vect n (Fin n)` and `Vect (n + 0) (Fin n)` are
-- the same type, but the type checker be like 🙅.

-- <Discuss decidability of equality again>

-- But they are ultimately the same thing! So what do we do here?
-- Recall that `Equals : a -> b -> Type`.
-- What if we let `a` and `b` be `Type` itself?
-- In Idris, types are terms of type `Type`, so we can use types
-- as indices.

Vect_plus_0_eq : (n : Nat) -> Vect (n + 0) (Fin n) = Vect n (Fin n)
-- ⬇️ Definition below ⬇️

-- Why so, precisely? LHS and RHS are of the form `Vect ?smth (Fin n)`,
-- where in ?smth two things that we know to be equal appear.

-- Recall:
plus_0_eq : {n : Nat} -> n = n + 0
plus_0_eq {n = 0} = Refl
plus_0_eq {n = S n'} = cong S (plus_0_eq)

Vect_plus_0_eq n = cong (\m => Vect m (Fin n)) (sym plus_0_eq)

-- So now we know that for types `a` and `b`, we can encode
-- the fact that they are the same by a term of type `a = b`

-- Then how can we use this to be able to give an `a` for a `b`?
-- We want to say, since i have `aeqb : a = b` and I have an `x : a`
-- then I can give `x` as if it were a `b`.

coerce : a = b -> a -> b
coerce {a = a'} {b = a'} Refl = id

forall_n_vect_n_0' : (n : Nat) -> Vect (n + 0) (Fin n)
forall_n_vect_n_0' n = coerce (sym (Vect_plus_0_eq n)) v
    where
    v : Vect n (Fin n)
    v = range

-- Let's take a deep breath. It took us two lectures
-- to be able to do this!

-- This pattern of swapping equal things on indices of
-- type families is pretty common, so we have a special
-- name for it:

transport : (0 fam : a -> Type) -> {x, y : a} -> x = y -> fam x -> fam y
transport fam prf z = coerce (cong fam prf) z

-- But I want to tell you about another way to do this.
-- We can start by defining transport:

transport' : (0 fam : a -> Type) -> {x, y : a} -> x = y -> fam x -> fam y
transport' fam Refl = id

-- And then we can define coerce in terms of transport:
coerce' : {a, b : Type} -> a = b -> a -> b
coerce' prf = transport' id prf

-- So using transport, our favourite definition becomes:
forall_n_vect_n_0'' : (n : Nat) -> Vect (n + 0) (Fin n)
forall_n_vect_n_0'' n = transport (\m => Vect m (Fin n)) plus_0_eq v
    where
    v : Vect n (Fin n)
    v = range

-- A more complex example

-- Recall from the previous lecture: addition is commutative
-- I may have flipped some equalities
plus_comm : (m, n : Nat) -> m + n = n + m
plus_comm 0 n = plus_0_eq
plus_comm (S m) n = 
    let
        IHm = plus_comm m n
    in Calc $
        |~ S (m + n)
        ~~ S (n + m) ...( cong S IHm )
        ~~ n + S m   ...( plus_S n m )

twisted_concat  :  {m , n : Nat} -> Vect m a -> Vect n a -> Vect (n + m) a
twisted_concat v w = 
    let vw = v ++ w
    in transport (\p => Vect p a) (plus_comm m n) vw

-- Remark: please do not use `rewrite`!

-- That's all for equality of types!

{-
    ######################
    #  Further Readings  #
    ######################
    
    (After typing this, Copilot suggested a URL about Univalent Foundations.
    Let's not go there for now 😅.)
    
    ** THE FOLLOWING IS NOT MANDATORY, NOT CURRICULAR AND NOT IN ANY WAY
       INFLUENTIAL FOR THE THE FINAL GRADE! **

    If you are interested in using programming languages for theorem proving,
    I personally learned about it through this book:
     - https://softwarefoundations.cis.upenn.edu/lf-current/index.html
    Note that you don't need any theoretical knowledge to go into it,
    but it does use a different dependetly typed programming language (Coq)
    which is more geared to theorem proving than Idris. Coq is also introduced
    in the book, you don't need to know it beforehand. Surely, having studied
    Idris gives you a head start.

    Another dependently typed language that doubles as a proof assistant,
    which is more similar to Idris, is Agda. If you want to see what it looks
    like, you might want to check out *part 1* of this book:
     - https://plfa.github.io/
    This goes over the topics of lectures 11-15 of our course. You will notice
    that as opposed to Coq, where one gives proof by listing the steps to take
    towards the goal (this is called tactic-based theorem proving), in Agda
    one does case splitting and writes terms to fill holes, in a way that is
    similar to Idris, maybe more interactive.

    We don't think that the theory of constructive logic/lambda calculus/programming
    languages belongs here, but if you are curious about it, you are always encouraged
    to ask questions!
-}
