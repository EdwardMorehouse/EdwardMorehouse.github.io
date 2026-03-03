# script file from lecture on 2024-02-06

def before(str1 , str2) :
    return str.lower(str1) < str.lower(str2)

def is_even(num) :
    return num % 2 == 0

def last_digit(num) :
    assert num >= 0
    return num % 10

def is_even_but_doesnt_end_in_4(num) :
    return \
    is_even(num) and \
    not last_digit(num) == 4

def remainder(numer , denom) :
    """ signature: (int , int) --> int """
    assert numer >= 0 and denom > 0 
    return numer % denom

def last_char(text) :
    assert len(text) > 0 , "the empty string is empty"
    return text[-1]

def p_n_r(x) : # print and return a value
    print("printing " + str(x))
    return x
