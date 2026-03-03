# script file from lecture on 2024-02-16

def initials(first , middle , last) :
    #plan
    #1. get the initals
    finitial = first[0]
    minitial = middle[0]
    linitial = last[0]
    #2. combine them to a string
    return finitial + '. ' + minitial + '. ' + linitial + '.'

def initials(first , middle , last) :
    return f'{first[0]}. {middle[0]}. {last[0]}.'

def middle_part(text) :
    return text[1 : -1]

def contains_at_least(items , num , item) :
    return list.count(items , item) >= num

def biggest_in_longest(list1 , list2) :
    #plan
    #1. determine which list is longest
    #2. get the largest element from that list
    if len(list1) >= len(list2) :
        return max(list1)
    else :
        return max(list2)

def biggest_in_longest(list1 , list2) :
    longest = list1 if len(list1) >= len(list2) else list2
    return max(longest)
    
