# script file from lecture on 2024-04-05

# signature:  list (tuple [str, int])
beatle_grades = [
    ("John"   , 94) ,
    ("Paul"   , 82) ,
    ("George" , 79) ,
    ("Ringo"  , 66) ]

def best_student(table) :
    ''' sig: (list (tuple (str , int))) --> str '''
    # try the accumulator pattern:
    (nerd_name , nerd_score) = ('NA' , 0)
    for (name , score) in table :
        if score > nerd_score :
            (nerd_name , nerd_score) = (name , score)
    return nerd_name

prices = \
   {'apple':0.50, 'banana':0.25, 'kiwi':1.00, 'lime':0.75}

my_order = [('banana', 2) , ('kiwi', 1) , ('lime', 1)]

def fruit_bill (order):
    ''' (list (tuple [str , int])) --> float '''
    # try the accumulator pattern:
    total = 0.0
    for (item , quantity) in order :
        total += prices[item] * quantity
    return total

