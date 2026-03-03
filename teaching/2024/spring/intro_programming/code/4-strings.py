# script file from lecture on 2024-02-01

# some strings:
size = 'large'
color = "blue"

line_1 = "don't ever"
line_2 = 'say "never"'
line_3 = "never say \"never\""
line_4 = 'don\'t say it!'

# a multi-line string:
two_cities = """\
It was the best of times,
it was the worst of times,
it was the age of wisdom,
it was the age of foolishness,
it was the epoch of belief,
it was the epoch of incredulity,
it was the season of Light,
it was the season of Darkness...
"""

# returning vs. printing:
def double(num) :
    return 2 * num

def print_double(num) :
    print(str(2 * num))

# evaluates the expression without effects:
double(2)

# prints a value and returns None:
# print_double(2)

# interacting with the user:
def greet(name) :
    """ signature: str --> NoneType """
    print("Hello " + name + "!")

def meet() :
     """ signature: () --> str """
     return input("What's your name? ")
    
def meet_and_greet() :
    name = meet()
    greet(name)

# type conversion functions:
def adder() :
    num1 = int(input("What is the first number? "))
    num2 = int(input("What is the second number? "))
    print("The sum is " + str(num1 + num2))
