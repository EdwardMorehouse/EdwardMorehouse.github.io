# script file from lecture on 2024-03-28

# pizza sizes: dict (str , int)
sizes = {"small":12 , "medium":16 , "large":20}

olympics = dict() # dict (int , str)
olympics[1896] = 'Thomas Burke'
olympics[1988] = 'Ben Johnson'
olympics[2008] = 'Usain Bolt'
olympics[2012] = 'Usain Bolt'
olympics[2016] = 'Usain Bolt'
olympics[1988] = 'Carl Lewis' # doping

years = olympics.keys()
winners = olympics.values()
records = olympics.items()

def lookup_all(dictionary , keys) :
    ''' (dict (a , b) , list a) --> list b '''
    # strategy: use the accumulator pattern
    values = []
    for key in keys :
        if key in dictionary.keys() :
            #values.append(dictionary[key])
            # or
            values += [dictionary[key]]
    return values

def remove_all(dictionary , target) :
    ''' (dict (a , b) , b) --> list a '''
    # strategy: use the accumulator pattern
    keys = []
    for (key , val) in dictionary.items() :
        if target == val :
            keys.append(key)
    for key in keys :
        del dictionary[key]
    return keys

def invert_dict(arg_dict) :
    ''' sig: (dict (a , b)) --> dict (b , set a) '''
    # strategy: use the accumulator pattern
    result_dict = dict()
    for (key , val) in arg_dict.items() :
        if val not in result_dict.keys() :
            result_dict[val] = set()
        result_dict[val].add(key)
    return result_dict

