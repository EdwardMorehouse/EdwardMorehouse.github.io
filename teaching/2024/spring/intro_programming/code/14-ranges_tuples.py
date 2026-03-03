# script file from class on 2024-02-27

def products (nums_1 , nums_2) :
    ''' sig: (list int , list int) --> list (list int) '''
    outer_acc = []
    for num_1 in nums_1 :
        inner_acc = []
        for num_2 in nums_2 :
            inner_acc.append(num_1 * num_2)
        outer_acc.append(inner_acc)
    return outer_acc

def compound_words(prefixes , suffixes) :
    words = []
    for prefix in prefixes :
        p_words = []
        for suffix in suffixes :
            word = prefix + suffix
            p_words.append(word)
        words.extend(p_words)
    return words

# In this case we need just one accumulator:
def compound_words(prefixes , suffixes) :
    words = []
    for prefix in prefixes :
        for suffix in suffixes :
            words.append(prefix + suffix)
    return words

def rearrange(items , indices) :
     ''' sig: (list a , list int) --> list a '''
     acc = []
     for index in indices :
         acc.append(items[index])
     return acc

import turtle

def regular_polygon(sides , length) :
    for _ in range(sides) :
        turtle.forward(length)
        turtle.left(360/sides)

def print_every_other(items) :
     ''' sig: (list a) --> NoneType '''
     for (index , item) in enumerate(items) :
         if index % 2 == 0 :
             print(str(item))

def indices(target , items) :
    acc = []
    for (index , item) in enumerate(items) :
        if item == target :
            acc.append(index)
    return acc
    
beatle_grades = \
 [  #  last       , first    , grade
     ("Lennon"    , "John"   , 94),
     ("McCartney" , "Paul"   , 82),
     ("Harrison"  , "George" , 79) ,
     ("Starr"     , "Ringo"  , 66)
]

def get_grade (record) :
     return record[2]
