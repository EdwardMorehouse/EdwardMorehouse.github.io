{--
 -- ITI0212 Lecture week 12, 2022-04-17
 --
 -- First-Order Logic
 --
 --}

module Lecture12

import Data.Fin

%default total

{-- First-Order Logic
    =================

    Two main topics today:

    1. Reasoning about "false" propositions:

      * How do we state that a certain proposition is false?

      * What does a proof of "negation" look like?

    2. Logical connectives:

      * How do we state the proposition "p and q", for propositions (p, q : Type)?

      * What about "p or q" and "p implies q"?

         (we already hinted at it in the previous lecture;
          today we try and make everything more precise)

      * Can we encode quantifiers ("for all (x : a), x is such that ...",
                                   "there exists an (x : a), such that ...")?
        => SPOILER: Yes, we can; and you've already done it yourself!
--}

{- ============================================================
    (A 5 minutes recap of the "proposition as types" paradigm)
   ============================================================ -}

-- Given a number n, the proposition IsEven n stating that n is even
data IsEven : Nat -> Type where
  -- you have a proof that 0 is even,
  IsEvenZ : IsEven 0
  -- for any n, if you have a proof that n is even, then S (S n) is even
  IsEvenSS : IsEven n -> IsEven (S (S n))

-- Given two numbers a and b, the proposition a <= b (a is less or equal than b)
data (<=) : (a : Nat) -> (b : Nat) -> Type where
  -- for any a, you have a proof that a is less or equal than 0
  LeZ : 0 <= a
  -- for any a and b, if a <= b then their successors are also less or equal
  LeS : a <= b -> S a <= S b

-- The type of animals (~= Fin 3)
data Animal : Type where
  Eagle : Animal
  Crow : Animal
  Pig : Animal

-- The proposition that an animal can fly only has two proofs, for Eagle and Crow
data CanFly : (a : Animal) -> Type where
  EaglesCanFly : CanFly Eagle
  CrowsCanFly : CanFly Crow

-- ===============================================

{-
  Reasoning about false statements
 -}

-- Let's encode the proposition 1 <= 0 as a type:
OneLessEqZero : Type
                -- This is just a proposition! (a Type)
                -- It does not evaluate to anything but itself
                -- in the same sense that the type Nat is just Nat.
OneLessEqZero = 1 <= 0

PigsCanFly : Type
                -- Again, this is just a proposition, a type.
                -- An impossible task: write a term with this type.
PigsCanFly = CanFly Pig

-- How can we assert that something is false
-- in the propositions-as-types interpretation?

-- It is going to look something like this:
NotOneLessEqZero : Type
                   -- The proposition "it is not true that 1 <= 0"
                   -- should certainly be inhabited! So we expect that
                   -- there *is* a term of type NotOneLessEqZero.
NotOneLessEqZero = Not (1 <= 0)

PigsCannotFly : Type
                   -- Ideally, we should be able to prove this.
                   -- This expresses the fact that `CanFly Pig` has no proof.
PigsCannotFly = Not PigsCanFly

-- ===============================================

{-
  The idea we will use to express negation:

    ***A proposition is false when it is `impossible` to prove.***

    ***We consider something as false exactly
       when there can be no proofs of it.***

    ***The proposition `P : Type` is false when
       there exist no terms (prf : P).***
-}

-- We've already seen a way simpler proposition for which there
-- were no proofs of it, from Lecture 2...

data Void' : Type where

  -- *No* constructors for this type:
  -- It is impossible to construct a term
  --    (prf : Void')
  -- i.e. a proof of an impossible statement.

-- => This type is in Prelude as `Void`.

-- ===============================================

-- It is trivial to construct a function *from* Void to any other type:
trivial : Void -> a
trivial x impossible
-- We define a function by pairing each (x : Void) with a term (y : a).
-- But there is not such `x`, So we have to cover 0 cases.


-- Under the propositions-as-type paradigm:
--    `trivial` is sometimes called the
--        "principle of explosion"
--    or
--        "ex falso sequitur quodlibet":
--        From falsity, anything follows.

-- Since you cannot construct something with type `Void`,
-- this function can never be called (unless you already assume something with type `Void`).

-- => `trivial` is available as `void` in Prelude.

-- ===============================================

-- What about a function from some type `a` *to* Void?
-- This is only possible in exactly two cases:            [assuming no bugs in Idris]

-- (1): the function is not total:

partial
hopeless : Nat -> Void   --  this function has the right type,
hopeless n = hopeless (S n)  --  but it will never return a value

-- (2) the other type is also empty:

pointless_fin : Fin 0 -> Void
pointless_fin x impossible

pointless_pigs_can_fly : CanFly Pig -> Void
pointless_pigs_can_fly EaglesCanFly impossible
pointless_pigs_can_fly CrowsCanFly impossible

pointless_1leq0 : 1 <= 0 -> Void
pointless_1leq0 LeZ impossible
pointless_1leq0 (LeS x) impossible

pointless_100leq2 : 100 <= 2 -> Void
pointless_100leq2 (LeS LeZ) impossible

{- The above reasoning shows:
    There is no proof of `p`.
      1) There *is not* a term (prf : p)
      2) There *is* a function (f : p -> Void)
-}

-- *This* is the trick we use to define negation: functions into Void.

-- ===============================================

{-  Negation as Refutation  -}

-- We can use a total function to the  Void  type to express
-- the negation of a proposition interpreted as a type.

Not' : Type -> Type
Not' a =  a -> Void

{-
 * An element of type `Not a` is a function sending
   elements of type `a` to elements of type `Void`.

 * But there are no elements of type `Void`.

 * So, if this function is total, then there can be
   no elements of type `a` either.

 * Thus `a` must be an empty type.

 * If we interpret the type `a` as a proposition,
   this means that it can have no proofs.

 * Which is what it means to assert that it is false.
 -}

not_one_less_eq_zero : Not (1 <= 0)
not_one_less_eq_zero = pointless_1leq0

pigs_cannot_fly : Not (CanFly Pig)
pigs_cannot_fly = pointless_pigs_can_fly

-- `Fin 0` is hard to interpret as a proposition: we can view this as saying
-- "it is impossible to construct an element of `Fin 0`"
--   or
-- "the type `Fin 0` is uninhabited."
there_is_no_fin_zero : Not (Fin 0)

two_plus_two_less_three_is_impossible : Not (2 + 2 <= 3)

-- ===============================================

{-  Examples with Negation  -}

-- From having both a proof and its negation I can prove anything.
contradiction : p -> Not p -> a
contradiction x f = absurd (f x)

example_contradiction : CanFly Pig -> 2 + 2 <= 3
example_contradiction prf_pigs_can_fly =
  contradiction prf_pigs_can_fly pigs_cannot_fly

lemma : Not (2 + 2 <= 3)
lemma (LeS (LeS (LeS LeZ))) impossible
lemma (LeS (LeS (LeS (LeS x)))) impossible

example_contradiction' : 2 + 2 <= 3 -> CanFly Pig
example_contradiction' two_p_two_le_three = contradiction two_p_two_le_three lemma

-- ===============================================

{-
  Second example: odd numbers

  Idea: number is odd exactly when it is not even.
-}
IsOdd : Nat -> Type
IsOdd n = Not (IsEven n)

-- Proposition: 1 is an odd number.
one_odd : IsOdd 1
one_odd IsEvenZ impossible
one_odd (IsEvenSS x) impossible
-- Proof: Get used to seing a lot of `impossible` cases:

-- Proposition: If n is even, then n + 1 is odd.
even_to_succ_odd : IsEven n -> IsOdd (S n)
even_to_succ_odd IsEvenZ = one_odd
even_to_succ_odd {n = S (S k)} (IsEvenSS is_even) = impossibility
  where 
    ind_hyp : IsOdd (S k)
    ind_hyp = even_to_succ_odd {n = k} is_even

    impossibility : IsEven (S (S (S k))) -> Void
    impossibility (IsEvenSS is_even_sk) = contradiction is_even_sk ind_hyp
-- Proof: By induction on n.

-- We can show that the successor of an odd number is even,
-- but we can't pattern match on the assumption  IsOdd n
-- because  IsOdd  is not an inductively defined type.
-- However, we can pattern match on its  Nat  index  n:
succ_odd_even  :  (n : Nat) -> IsOdd n -> IsEven (S n)


-- ===============================================

{-- An interface for empty types

  Always working with functions `p -> Void` is cumbersome.

  The `Uninhabited` interface can only be implemented for "empty"
  types, in particular for propositions that do not hold:
--}
interface Uninhabited' (0 a : Type) where
  uninhabited' : Not a

implementation Uninhabited (1 <= 0) where
  uninhabited = not_one_less_eq_zero

implementation Uninhabited (CanFly Pig) where
  uninhabited = pigs_cannot_fly

implementation Uninhabited (IsEven 1) where
  uninhabited = one_odd

-- We can restrict types of a polymorphic function to empty types:
absurd' : (Uninhabited' a) => a -> b
absurd' x = void $ uninhabited' x
-- => Available as `absurd` in Prelude.

implementation Uninhabited (S m <= 0) where
  uninhabited prf impossible

implementation [MyImpl] (Uninhabited (m <= n)) => Uninhabited (S m <= S n) where
  uninhabited (LeS x) = uninhabited x

contradiction' : Uninhabited' p => p -> a
contradiction' p = void $ uninhabited' p

-- ===============================================

{-- Logical connectives
    ===================

  * and, or: "P and Q hold", "P or Q holds"
  * implication: "If P, then Q"
  * existential/universal quantification:

    - "For all (x : a), P(x) holds"

    - "There exists some (x : a) such that P(x) holds"
--}

-- Logical disjunction ("or"):
--
--   To prove that "a or b" holds, either provide...
--   * ... a proof of "a holds"
--   * or a proof of "b holds"
data Or : (a : Type) -> (b : Type) -> Type where
  ProofLeft  : (prf : a) -> Or a b
  ProofRight : (prf : b) -> Or a b

-- Proposition: "Crows might fly, or pigs might fly."
or_example : CanFly Crow `Or` CanFly Pig
or_example = ProofLeft CrowsCanFly
-- Proof: We know that crows might fly.  This is enough to prove the statement.


-- The type (Or p q) is not in the standard library.
-- But (Either p q) is completely equivalent, except that its constructors are
-- named differently.  Try it in the REPL:
--
-- Lecture12> :doc Either
-- data Prelude.Either : Type -> Type -> Type
--   ...
--   Constructors:
--     Left : a -> Either a b
--       ...
--     Right : b -> Either a b
--       ...
--

Or' : Type -> Type -> Type
Or' = Either

-- The same proposition, but written with the Either type:
or_example' : Either (CanFly Crow) (CanFly Pig)
or_example' = Left CrowsCanFly

left_impossible : (Uninhabited a) => a `Or` b -> b
left_impossible (ProofLeft prf_a) = contradiction prf_a uninhabited
left_impossible (ProofRight prf_b) = prf_b

-- ===============================================

-- Logical conjunction ("and"):
--
--   To prove that "p and q" holds, we need to...
--    - provide of p
--    - *and* a proof of q
data And : (p : Type) -> (q : Type) -> Type where
  Both : (prf_of_p : p)
      -> (prf_of_q : q)
      -> And p q

-- Proposition: Crows might fly, and pigs don't fly.
and_example : CanFly Crow `And` Not (CanFly Pig)
and_example = Both CrowsCanFly pigs_cannot_fly
-- Proof: We use the proofs
--    * CrowsCanFly : CanFly Crow
--    * pigs_cannot_fly : Not (CanFly Crow)
--    ...from above to construct the correct term.

-- Again, this type is not in the standard library, but
-- is equivalent to another type:
--
--  Lecture12> :doc Pair
--  data Builtin.Pair : Type -> Type -> Type
--    The non-dependent pair type, also known as conjunction.
--                                               ^^^^^^^^^^^
--    ...
--    Constructor: MkPair : a -> b -> (a, b)
--                 ^^^^^^ we called this `Both`
--
-- (a , b) is syntactic sugar for (Pair a b).
And' : Type -> Type -> Type
And' = Pair

-- The same proposition, but written with the Pair type:
and_example' : Pair (CanFly Crow) (Not (CanFly Pig))
and_example' = (CrowsCanFly, pigs_cannot_fly)

-- ===============================================

-- Logical implication ("implies")
--
-- A proof of the proposition  a Implies b
-- is a function sending any proof of the proposition `a`
-- to a proof of the proposition `b`.
Implies  :  (a : Type) -> (b : Type) -> Type
Implies a b  =  a -> b

eg_implies  :  (n <= m) `Implies` (S n <= S m)
eg_implies n_le_m = LeS n_le_m


eg_implies'  :  n <= m   ->   S n <= S m
eg_implies' = LeS

-- ===============================================

-- With dependent types, we can define the "for all ..."-quantifier:
--
-- Assuming we have a proposition indexed by values of type `a`,
--    p : (x : a) -> Type
-- We encode "For all (x : a), p(x) holds"
-- as a function
--    prf : (x : a) -> p x
--
-- Since `p` is a family of types depending on values of type `a`,
-- `IsEven x` and `IsEven y` are different propositions for different `x, y`,
-- This is the same thing as saying that the proposition IsOdd 4
-- is different from the proposition IsOdd 7.

-- Proposition: For all (n : Nat), n is less or equal to itself.
-- Proof:  We need to give a function
--            prf : (n : Nat) -> n <= n
--         So to each `n`, we associate a proof `n <= n`.

less_than_eq_reflexive : (n : Nat) -> n <= n
less_than_eq_reflexive 0 = LeZ
less_than_eq_reflexive (S k) = 
  let iH = less_than_eq_reflexive k
   in LeS iH

lemma2 : (m : Nat) -> (n : Nat) -> S n <= S m -> n <= m
lemma2 0 0 x = LeZ
lemma2 0 (S k) (LeS x) = x
lemma2 (S k) 0 x = LeZ
lemma2 (S k) (S j) (LeS x) = LeS (lemma2 k j x)




-- Proposition: For all animals, either it flies or it does not.
every_animal_flies_or_does_not : (a : Animal) -> CanFly a `Or` Not (CanFly a)
every_animal_flies_or_does_not Eagle = ProofLeft EaglesCanFly
every_animal_flies_or_does_not Crow = ProofLeft CrowsCanFly
every_animal_flies_or_does_not Pig = ProofRight pigs_cannot_fly

-- ===============================================

-- With dependent types, we can define the "there exists ..."-quantifier:
--
-- A proof of the proposition that some element
-- of the type `a` satisfies the predicate  p
-- is an `element` of type `a` together with
-- a proof of the proposition that `element` satisfies `p`.

data Exists : (t : Type) -> (p : t -> Type) -> Type where
  ProofExists : (element : t)
             -> (proof_of_p : p element)
             -> Exists t p

example_exists  :  Exists Nat IsEven
example_exists = ProofExists 2 (IsEvenSS IsEvenZ)

Exists' : (a : Type) -> (p : a -> Type) -> Type
Exists' = DPair

example_exists' : DPair Nat IsEven
example_exists' = (2 ** (IsEvenSS IsEvenZ))

-- The kind of constructive logic that this
-- propositions-as-types interpretation realizes
-- is called "intuitionistic logic".


-- A or (not A)

data PI : Type -> (a -> Type) -> Type where
  La : ((x : a) -> b x) -> PI a b 
