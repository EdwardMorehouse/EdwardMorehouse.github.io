# script file from class on 2024-05-03

def my_range(stop) :
    num = 0
    while num < stop :
        yield num  # can pick up where we left off
        num += 1

def plus_minus(stop) :
    num = 1
    while num < abs(stop) :
        yield num
        yield (-1 * num)
        num += 1

def add(x , y) :
    ''' sig: (int , int) --> int '''
    return x + y

def add_c(x , y , cont) :
    ''' sig: (int , int , fun (int -> a)) --> a '''
    return cont(x + y)

def parity_c(num , even_cont , odd_cont) :
    ''' sig: (int , fun (int -> a) , fun (int -> a)) --> a '''
    return even_cont(num) if num % 2 == 0 else odd_cont(num)

def divide_c(x , y , cont) :
    if y != 0 :
        return cont(x / y)
    else :
        print("Can't divide by 0!")

