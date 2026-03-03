# script file from class on 2024-04-19

def quick_sort(items) :
    ''' sig: (list int) --> list int '''
    if len(items) < 2 :
        return items.copy()
    else :
        pivot = items[0]
        tail = items[1: ]
        (upper , lower) = ([] , [])
        for item in tail :
            (lower if item <= pivot else upper).append(item)
        sorted_upper = quick_sort(upper)
        sorted_lower = quick_sort(lower)
        return sorted_lower + [pivot] + sorted_upper

def merge(xs , ys) :
    ''' sig: (list int , list int) --> list int '''
    if xs == [] or ys == [] :
        return xs + ys
    else :
        if xs[0] < ys[0] :
            return [xs[0]] + merge(xs[1: ] , ys)
        else :
            return [ys[0]] + merge (xs , ys[1: ])


      
