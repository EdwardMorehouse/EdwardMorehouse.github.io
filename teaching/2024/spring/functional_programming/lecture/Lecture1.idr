{-- 
 -- Bowdoin CSCI 2520
 --
 -- Functional Programming
 --
 -- week 1 (2024-01-22)
 -- 
 -- Course Introduction
 --}


{--
	(1) Why learn (dependently typed) (functional programming)?
	
	functional programming:
	* functions are data
		- higher-order algorithms
	* computation by expression evaluation
		- static guarantees for effects
	* mathematical semantics
	
	(dependent) types:
	* types are specifications
		- dynamic vs static type checking
			https://youtu.be/6pDH66X3ClA
			https://youtu.be/ph9HGYkAiWw
		- specification reliability
			Tony Hoare's "billion-dollar mistake"
	* interactive program development
	* types are data
		- types can appear in definitions of types or terms
			(generics)
		- terms can appear in definitions of types
			(indexed types)
	* reduce built-ins
		- definability of many common types and data structures, partiality, arbitrary tuples, printf's type, etc.
	* more precise specifications
	* proofs of program correctness
		- propositions as types
	
	the Idris programming language
 --}


{--
	(2) What is the structure of this course?

		See syllabus at
		bowdoin-csci-2520.github.io
 --}


{--
	(3) Installing and configuring tools

		See lab 1
 --}


{--
	(4) Getting started with Idris
 --}

module Lecture1

s  :  String
s  =  "hello"

greet  :  String -> String
greet x  =  s ++  " " ++ x

n  :  Integer
n  =  21

double  :  Integer -> Integer
double num  =  num * 2
