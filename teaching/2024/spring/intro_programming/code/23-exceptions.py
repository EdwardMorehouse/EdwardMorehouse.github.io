# script file from lecture on 2024-04-02

def is_int_string(text) :
    '''
    sig: (str) --> bool
    determines if a string is parseable as an int
    '''
    return str.isdigit(text) or \
    (text[0:1] == '-' and str.isdigit(text[1:]))

def cautious_interactive_division() :
    x_str = input('please enter the numerator: ')
    y_str = input('please enter the denominator: ')
    if is_int_string(x_str) and is_int_string(y_str) :
        # it's safe to parse ints from them
        (x_int , y_int) = (int(x_str) , int(y_str))
        if y_int != 0 :
            # it's safe to divide them
            result = x_int / y_int
            print(f"{x_str} / {y_str} = {result}")
        else :
            print("you can't divide by zero")
    else :
        print('to divide you must enter two numbers')

def brash_interactive_division() :
    x_str = input('please enter the numerator: ')
    y_str = input('please enter the denominator: ')
    try :
        x_int = int(x_str)     # possible ValueError
        y_int = int(y_str)     # possible ValueError
        result = x_int / y_int # possible ZeroDivisionError
        print(f"{x_str} / {y_str} = {result}")
    except ZeroDivisionError :
        print("you can't divide by zero")
    except ValueError :
        print('to divide you must enter two numbers')  

# sig: dict (str , set str)
day_dict = {
   'm':{'Monday'}, 'w':{'Wednesday'}, 'f':{'Friday'}, 'b':{},
   't':{'Tuesday','Thurdsday'}, 's':{'Saturday','Sunday'}}

def print_some (dictionary , key) :
    ''' sig: (dict (a , set b) , a) --> NoneType '''
    try :
        candidates = dictionary[key]  # possible KeyError
        result = list(candidates)[0]  # possible IndexError
        print(f"{result}")
    except (KeyError , IndexError) :
        print("No can do")

def average (nums) :
    try :
        acc = 0
        for num in nums :
            acc += num
        return acc / len(nums) # might divide by 0
    except ZeroDivisionError :
        return 0.0


