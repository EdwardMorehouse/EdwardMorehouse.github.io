
{--
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- Week 11, 2023-04-10
 -- 
 -- Propositions as Types
 --
 --}

module Lecture11

{- WHAT IS MATH?
=======================
  It is making statements and proving that they are true.

    Statement: "The square root of two is not rational."
    Proof:     "If it was a/b, then we would have a^2 = 2b^2, leading to both a and b being even, ..."


    Statement: "(cos(x) + i*sin(x))^n = cos(nx) + i*sin(nx)"
    Proof:     "We use the exp representation: 
                  (cos(x) + i*sin(x))^n = exp(ix)^n
                                        = exp(inx)
                                        = cos(nx) + i*sin(nx)" 


    Statement: "For all n > 2, and x, y, z, strictly postive integers, x^n + y^n != z^n."
    Proof:     "All semistable elliptic curves are modular, but then any solution of the equation above would create a Frey curve
                that is elliptic semistable but not modular."


  There is a crucial problem with this approach:
    -- Proofs are not mathematical objects -- 

  Proof are "meta" data associated to each statement, that human look at and agree upon.

  How do we know a proof is correct?
  -- We don't, we just stare at it long enough without finding any mistakes.

  That's a sad perspective for mathematics, isn't it?
  (see. FLT, Kapranov-Voevodsky)
-}


{-
  A first iteration: Predicates
  ==============================

  What is a proposition? It is something that is either true or false...

  We could consider a statement as a function to the "truth"-values

    True, False : Bool

  After all, a statement is either true or false, right?

  => functions `f : a -> Bool` are called "predicates"
-}


-- evenness of natural numbers as a predicate:
isEven' : Nat -> Bool
isEven' 0 = True
isEven' (S 0) = False
-- is k + 2 even? if and only if k is even
isEven' (S (S k)) = isEven' k


isEven'Four : Bool
isEven'Four = isEven' 4

isEven'Two : Bool
isEven'Two = isEven' 2

isEven'One : Bool
isEven'One = isEven' 1




-- There's little way to distinguish proofs:
sameProof : Bool
sameProof = isEven'Four == isEven'Two




{- There's also no way to inspect proofs:

    "Proofs" of `1 + 1 == 2` and Fermat's Last Theorem have the same value.

    But one is (way) more complicated to prove than the other.
-}


%default total

{-
  A second iteration: Proposition as types
  ==============================
  
  A proposition is something that requires *evidence*.
  It is a type.

  A proof of a propostion is an *evidence*.
  It is a term.

  p : P
  it means: p is a term/proof of type/proposition P  
  -----
  ...to show that a proposition is true in type theory corresponds to exhibiting an element [term] of the type corresponding to that proposition. 
     We regard the elements of this type as evidence or witnesses that the proposition is true. 
     (They are sometimes even called proofs...)

  (from Homotopy Type Theory – Univalent Foundations of Mathematics, section 1.11)
  -----

  A *proposition* is the collection of all of its *proofs*.
  A *type*        is the collection of all of its *terms* .


  We will...

    * construct types that encode logical statements, called "propositions"
    * construct terms of such types that encode their proofs

  This is known as "Propositions as Types".

  **This allows us to work with proofs as objects in their own regard:**
    Proving big conjectures from smaller theorems.
    Constructing big terms from smaller terms.

 -}

-- Evenness of Nats as an dependent type.

-- This type means that
-- if t : IsEven n then t is a proof that n is even.
data IsEven : (n : Nat) -> Type where
  IsEvenZ : IsEven 0
  IsEvenSS : IsEven n -> IsEven (S (S n))


isEvenZero : IsEven 0
isEvenZero = IsEvenZ

isEvenFour : IsEven 4
isEvenFour = IsEvenSS (IsEvenSS isEvenZero)

isEvenSix : IsEven 6
isEvenSix = IsEvenSS isEvenFour

{- Observation:

    Functions from propositions to propositions are logical
    implications:

      lemma : A -> B
      lemma p = ?q

      "Given a proof (p : A), construct a proof (?q : B)".

    In the body of `lemma`, pa` acts as an assumption that we can inspect.

    Let's give an example...
-}

--The identity function proves that for all propostion a, a implies a
-- lemma : a -> a
-- lemma x = x


-- If n + 2 is even, then n is even.
isEvenPP : IsEven (S (S n)) -> IsEven n
-- x : IsEven (S (S n)) AND IsEvenZ : IsEven 0
isEvenPP IsEvenZ impossible 
isEvenPP (IsEvenSS x) = x

-- The sum of two even numbers is even.
isEvenPlus : IsEven p -> IsEven m -> IsEven (p + m)
-- x : IsEven p == IsEvenZ : IsEven 0 
--   IsEven (p + n)
isEvenPlus IsEvenZ y = y
isEvenPlus (IsEvenSS x) y = IsEvenSS (isEvenPlus x y)


-- The product of two evens is even.
isEvenMul : IsEven p -> IsEven n -> IsEven (p * n)
-- p = 0
isEvenMul {p = 0} {n = n} IsEvenZ y = IsEvenZ
-- p = (S (S n))
-- IsEven (plus n (plus n (mult k n))) == IsEven (n + (n + (k * n)))
isEvenMul {p = (S (S k))} {n = n} (IsEvenSS x) y = isEvenPlus y (isEvenPlus y ih) where
  ih : IsEven (mult k n)
  ih = isEvenMul x y



{- Second Example: The "... is prefix of ..." relation as an dependent type. -}

-- "ab" is a prefix of "abcd"
-- "a" is NOT a prefix of "bcd"
-- "" is a prefix of everything

data IsPrefix : (xs : List a) -> (ys : List a) -> Type where
  IsPrefixNil : IsPrefix [] ys
  -- If xs is a prefix of ys, z::xs is a prefix of z::ys
  -- For instance "abc" is a prefix of "abcd", thus z::"abc" is a prefix of z::"abcd"
  IsPrefixCons : IsPrefix xs ys -> IsPrefix (z::xs) (z::ys)



-- If (z :: xs) is a prefix of (z :: ys), then the tail xs is a prefix of the tail ys.

isPrefixTail : IsPrefix (z::xs) (z::ys) -> IsPrefix xs ys
-- x           : IsPrefix (z::xs) (z::ys)
-- IsPrefixNil : IsPrefix [] ys
-- We see that x != IsPrefixNil
isPrefixTail IsPrefixNil impossible
isPrefixTail (IsPrefixCons p) = p


-- The prefix-relation is reflexive.
-- i.e. "abcd" is a prefix of "abcd"
-- i.e. "" is a prefix of ""
isPrefixRefl : (xs : List a) -> IsPrefix xs xs
isPrefixRefl [] = IsPrefixNil
isPrefixRefl (x :: xs) = IsPrefixCons (isPrefixRefl xs)
--isPrefixRefl is a PROOF that for all list xs, xs is a prefix of xs 

-- The prefix-relation is transitive.
isPrefixTrans : IsPrefix xs ys -> IsPrefix ys zs -> IsPrefix xs zs 
isPrefixTrans {xs = []} {ys = ys} {zs = zs} IsPrefixNil _ = IsPrefixNil
isPrefixTrans {xs = (z :: xs)} {ys = (z :: ys)} {zs = (_ :: zs)} (IsPrefixCons x) (IsPrefixCons y) = 
  IsPrefixCons (isPrefixTrans x y)


{- Third Example : Less Or Equal Than -}

data (<=) : (p : Nat) -> (n : Nat) -> Type where
  LeZ : 0 <= n
  -- For instance if t : 3 <= 4 then LeS t : 3 + 1 <= 4 + 1
  LeS : p <= n -> S p <= S n

-- <= is reflexive
leRefl : (n : Nat) -> n <= n
leRefl 0 = LeZ
leRefl (S k) = LeS (leRefl k)

-- p <= p + n
lePlus : (p : Nat) -> (n : Nat) -> p <= p + n
-- p = 0, the statement becomes 0 <= 0 + n
lePlus 0 n = LeZ
lePlus (S k) n = LeS (lePlus k n)
-- lePlus : p <= p + n
-- so in the Propostions as Type paradigm
-- lePlus is a PROOF that p <= p + n


-- Can we prove n <= m + n?
-- We can try, but we will fail, for that we will need to know what is EQUALITY.
-- lePlus' : (p : Nat) -> (n : Nat) -> p <= n + p
-- plus 0 n ==== n (by definition of the plus function)
-- plus n 0 = n, this will require a proof
-- t : plus n 0 = n
-- lePlus' 0 n = ?lePlus'_rhs_1
-- lePlus' (S k) n = ?lePlus'_rhs_2


-- le of lt
data (<) : (p : Nat) -> (n : Nat) -> Type where
  LtZ : 0 < S n
  LtS : p < n -> S p < S n

leOfLt : (p : Nat) -> (n : Nat) -> p < n -> p <= n
leOfLt 0 (S n) LtZ = LeZ
leOfLt (S p) (S n) (LtS x) = LeS (leOfLt p n x)


{- Induction -}
-- We saw it already in plenty of example, we can reason by induction.

-- induction principle on Nat
-- P is a proposition / a statement
-- We want to prove that for all n : Nat, P n
-- Base case: we give a proof of P 0
-- Inductive step: Suppose we have proved it for P n, then we prove it for P (n + 1)
-- By induction, for all n, P n

-- IsEven : (n : Nat) -> Type 
induction : (prop : Nat -> Type) -> 
  (base_case : prop 0) -> 
  (induction_step : (k : Nat) -> prop k -> prop (S k)) -> 
  (n : Nat) -> prop n
induction prop base_case induction_step 0 = base_case
induction prop base_case induction_step (S k) = induction_step k (induction prop base_case induction_step k)


-- let us use it to prove that n * 2 is even
isEvenMulTwo : (n : Nat) -> IsEven (n * 2)
isEvenMulTwo n = induction (\ n => IsEven (n * 2)) IsEvenZ ind_step n where
  ind_step : (k : Nat) -> IsEven (mult k 2) -> IsEven (S (S (mult k 2)))
  ind_step k x = IsEvenSS x

