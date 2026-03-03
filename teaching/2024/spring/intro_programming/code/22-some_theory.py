# script file from lecture on 2023-10-19

def dict_from(pairs) :
    results = {}
    for (key , val) in pairs :
        results[key] = val
    return results

def invert_dict(arg_dict) :
    new_dict = {}
    for (key , val) in arg_dict.items() :
        if val not in new_dict :
            new_dict[val] = []
        new_dict[val].append(key)
    return new_dict
