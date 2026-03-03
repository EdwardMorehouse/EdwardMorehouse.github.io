# script file from lecture on 2024-04-16

import turtle

def countdown(n) :
    if n <= 0 :
        print('go!')
    else :
        print(f'{n}')
        countdown(n-1)

def factorial_iter(n) :
    acc = 1
    while n > 0 :
        acc *= n
        n -= 1
    return acc

def factorial_rec(n) :
    if n == 0 :
        return 1
    elif n > 0 :
        pred_fact = factorial_rec(n-1)
        return n * pred_fact

def tree(size , depth) :
    if depth <= 0 :
        pass
    else :
        turtle.forward(size)
        turtle.left(30.0)
        tree(4/5*size , depth-1)
        turtle.right(60.0)
        tree(4/5*size , depth-1)
        turtle.left(30.0)
        turtle.back(size)

def sierpinski_triangle(size , depth) :
    if depth > 0 :
        for i in range(3) :
            sierpinski_triangle(size/2 , depth-1)
            turtle.forward(size)
            turtle.left(120.0)

