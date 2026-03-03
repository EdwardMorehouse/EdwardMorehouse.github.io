# script file from lecture on 2024-05-02

def compose(f , g) :
    ''' sig: (fun (a -> b) , fun (b -> c)) --> fun (a -> c) '''
    return lambda x : g(f(x))

double = lambda x : 2 * x
succ = lambda x : x + 1

two_x_plus_one = compose(double , succ)

two_x_plus_two = compose(succ , double)

def identity(x) :
    ''' sig: (a) --> a '''
    return x

def iterate(n , f) :
    ''' sig: (int , fun (a -> a)) --> fun (a -> a) '''
    if n > 0 :
        return compose(f , iterate(n - 1 , f))
    else :
        return identity

eight_x = iterate(3 , double)

one_x = iterate(0 , double)

def compose_all(fs) :
    if fs != [] :
        return compose(fs[0] , compose_all(fs[1: ]))
    else :
        return identity

four_x_plus_two = compose_all([double, succ, double])

print_length = compose_all([len, str, print])

''' fun (int , int -> int) '''
mult = lambda x , y : x * y

''' fun (int -> fun (int -> int)) '''
mult_c = lambda x : lambda y : mult(x , y)

def curry(f) :
    ''' sig: (fun (a , b -> c)) --> fun (a -> fun (b -> c)) '''
    return lambda x : lambda y : f(x , y)

# : fun (list int -> list int)
double_all = curry(map)(double)

# : fun (list int -> list int)
just_evens = curry(filter)(lambda n : n % 2 == 0)

# sig: fun (list str -> int)
longest_string = compose(curry(map)(len) , max)

