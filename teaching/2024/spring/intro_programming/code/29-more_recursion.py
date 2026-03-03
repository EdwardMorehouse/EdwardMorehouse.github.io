# script file from class on 2024-04-18

'''
Interpolated string formatting:
https://fstring.help/cheat/
'''

def countdown(n) :
    if n > 0 :
        print(f'{n}')
        countdown(n-1)
    else :
        print('go!')

def is_palindrome(text) :
    '''sig: (str) --> bool '''
    if text == '' :
        return True
    else :
        return text[0] == text[-1] and is_palindrome(text[1:-1])

import turtle

def earring(size , hoops) :
    ''' sig: (int , int) --> NoneType '''
    if hoops > 0 :
        turtle.circle(size)
        earring(4/5 * size , hoops - 1)

def rev_list(items) :
    ''' sig: (list a) --> list a '''
    if items == [] :
        return []
    else :
        return rev_list(items[1: ]) + [items[0]]

def fib(n) :
    '''sig: (int) --> int '''
    if n in [0, 1] :
       return n
    else :
       return fib(n-2) + fib(n-1)

def crinkle(size , depth) :
    if depth <= 0 :
        turtle.forward(size)
    else :
        crinkle(size/3 , depth-1)
        turtle.right(60)
        crinkle(size/3 , depth-1)
        turtle.left(120)
        crinkle(size/3 , depth-1)
        turtle.right(60)
        crinkle(size/3 , depth-1)

def snowflake(size , depth) :
    for _ in range(3) :
        crinkle(size , depth)
        turtle.left(120)
