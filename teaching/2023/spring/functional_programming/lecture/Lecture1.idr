{-- 
 -- TalTech ITI0212
 --
 -- Functional Programming
 --
 -- week 1, 2023-01-30
 -- 
 -- Course Introduction
 --}



{--
	(1) Why learn dependently typed functional programming?
	
	functional programming:
	* functions as data
		- higher-order algorithms
	* computation as expression evaluation
		- static guarantees for effects
	* mathematical semantics
	
	dependent types:
	* types as specifications
		(https://youtu.be/6pDH66X3ClA)
		- static vs dynamic type checking
		- accuracy of specifications
	* interactive program development
	* types as data
		- Types can appear in definitions of types or terms
			(generics)
		- Terms can appear in definitions of types
			(indexed types)
	* reduce built-ins
		- definability of partiality, arbitrary tuples, printf, etc.
	* more precise specifications
	* proofs of program correctness
		(propositions as types)
	
	the Idris programming language
 --}




{--
  (2) What is the structure of this course?

    See syllabus

 --}




{--
	(3) Getting started with Idris
 --}

module  Lecture1
s  :  String
s = "hello"

greet : String -> String
greet x  =  s ++ " " ++ x

n : Integer
n = 42

double  :  Integer -> Integer
double num  =  num * 2
