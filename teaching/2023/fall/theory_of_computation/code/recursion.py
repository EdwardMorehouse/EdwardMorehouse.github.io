# Example of recursion by fixed point in python
# from class discussion on 2023-11-13 and 2023-11-29

# Curry's fixed-point combinator:
Y = lambda f : \
     (lambda x : f (lambda y : x (x) (y))) \
     (lambda x : f (lambda y : x (x) (y)))

# recursive factorial function:
fact = lambda n : 1 if n == 0 else n * fact (n - 1)

# term F such that fact = F (fact):
F = lambda f : lambda n : 1 if n == 0 else n * f (n - 1)
# so fact = Y (F)

# The same thing, but without using lambda:

def fact (n) :
  if n == 0 :
    return 1
  else :
    return n * fact (n - 1)

def F (f) :
  def inner(n) :
    if n == 0 :
      return 1
    else :
      return n * f (n - 1)
  return inner

