# script file from lecture on 2024-02-15

def my_insert(items , index , item) :
    """
    signature: (list a , int , a) --> NoneType
    inserts item at index of items list
    """
    items[index:index] = [item]

def my_pop(items , index) :
    """
    signature: (list a , int) --> a
    removes element at index from items and returns it
    """
    thing = items[index]
    items[index : index + 1] = []
    return thing
