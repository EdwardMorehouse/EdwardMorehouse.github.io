# script file from lab on 2024-02-29

#signature:  list (tuple [str, str, int])
beatle_grades = \
[   #  last         ,  first   , grade
    ("Lennon"       , "John"   , 94) ,
    ("McCartney"    , "Paul"   , 82) ,
    ("Harrison"     , "George" , 79) ,
    ("Starr"        , "Ringo"  , 66)
] 

def get_grade(record) :
    return record[2]

def average_grade(table) :
    total = 0
    for row in table :
        total += get_grade(row)
    return total / len(table)

import random

def flip() :
    return random.choice(["heads", "tails"])

def flip_until_heads() :
    coin = flip()
    print(coin)
    while coin != "heads" :
        coin = flip()
        print(coin)

def flip_until_heads() :
    coin = ""  # carefully chosen initial value
    while coin != "heads" :
        coin = flip()
        print(coin)

def flip_until_same() :
    (coin1 , coin2) = ("" , "anything")
    while coin1 != coin2 :
        (coin1 , coin2) = (flip() , flip())
        print(f'{coin1} , {coin2}')

def flip_until_head_run(num) :
    heads = 0
    while heads < num :
        coin = flip()
        print(coin)
        heads = heads + 1 if coin == 'heads' else 0
