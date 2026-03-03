# script file from class on 2024-03-26

beatles = {"John", "Paul", "George", "Ringo"} # : set str

nums = set(range(10)) # : set int
nothing = set()

def greet_all(collection) :
    for item in collection:
        print(f"hello {item}!")

(small , even) = ({0, 1, 2, 3, 4} , {0, 2, 4, 6, 8})

def symm_diff(A , B) :
    ''' sig: (set a , set a) --> set a '''
    return (A - B) | (B - A)
    #return (A | B) - (A & B)   

def proper_superset(A , B) :
    ''' sig: (set c , set c) --> bool '''
    return B <= A and A != B

