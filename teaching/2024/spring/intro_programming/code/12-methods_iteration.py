# script file from lecture on 2024-02-22

def print_each(items) :
    """
    signature: (list a) --> NoneType
    prints each item in a list
    """
    for item in items :
        print(str(item))

def sum_list(nums) :
    sum = 0              # initialize accumulator
    for num in nums :    # iterate over list
        sum = sum + num  # update accumulator
    return sum           # use the result

def count_evens(nums) :
    """signature: (list int) --> int"""
    acc = 0
    for num in nums :
        if num % 2 == 0 :
            acc += 1
    return acc
# or using a conditional expression:
def count_evens(nums) :
    acc = 0
    for num in nums :
        acc += 1 if num % 2 == 0 else 0
    return acc

def reverse_list(items) :
    """signature: (list a) --> list a"""
    acc = []
    for item in items :
        acc = [item] + acc
    return acc
# or using the list.insert method:
def reverse_list(items) :
    acc = []
    for item in items :
        acc.insert(0 , item)
    return acc

