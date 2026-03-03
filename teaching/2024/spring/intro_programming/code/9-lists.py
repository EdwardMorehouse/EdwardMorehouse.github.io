# script file from lecture on 2024-02-13

def reverse_sorted(items) :
    ''' (list a) --> list a '''
    return list(reversed(sorted(items)))

def rev_string(text) :
    ''' (str) --> str '''
    # plan:
    # turn string into list X
    text_list = list(text)
    # reverse list X
    rev_text_list = reversed(text_list)
    # turn list into string X
    joined_rev_text = str.join("" , rev_text_list)
    # return string X
    #return joined_rev_text
    # or just
    return str.join('' , reversed(list(text)))
