# script file from lecture on 2024-01-30

import math

def circle_area(radius) :
    area = math.pi * radius ** 2
    return area

def distance(x0 , y0 , x1 , y1) :
    '''
    sig: (float, float, float, float) --> float
    Returns the distance between
    point (x0 , y0) and (x1 , y1).
    '''
    base = x1 - x0
    height = y1 - y0
    dist = math.sqrt(base**2 + height**2)
    return dist

x = 1
y = x * 2
z = x + y
def f(x , y) :
    z = x + y
    return z
def g(z) :
    z = x + y
    return z

def F_to_C(fahrenheit) :
    '''
    signature: (float) --> float
    Converts temperature from F to C.
    '''
    return 5/9 * (fahrenheit - 32.0)

