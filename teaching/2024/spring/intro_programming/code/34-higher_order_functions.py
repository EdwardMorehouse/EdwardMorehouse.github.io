# script file from lecture on 2024-04-30

double = lambda num : 2 * num

is_even = lambda num : num % 2 == 0

add = lambda x , y : x + y

times_4 = lambda x : x * 4

square = lambda x : x * x

times = lambda x , y : x * y

def call(function , argument) :
    ''' sig: (fun (a -> b) , a) --> b '''
    return function(argument)

def list_map(f , items) :
    ''' sig: (fun (a -> b) , list a) --> list b '''
    acc = []
    for item in items :
        acc.append(f(item))
    return acc

# sig: (list str) --> list str
initials = lambda strings : \
    map(lambda string : string[0] , strings)

def list_filter(p , items) :
    ''' sig: (fun (a -> bool) , list a) --> list a '''
    acc = []
    for item in items :
        if p(item) :
            acc.append(item)
    return acc

def list_reduce(f , init , items) :
    ''' sig: (fun (b , a -> b) , b , list a) --> b '''
    acc = init
    for item in items :
        acc = f(acc , item)
    return acc
