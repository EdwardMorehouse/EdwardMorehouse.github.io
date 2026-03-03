# script file from lecture on 2024-04-04

def parse_numbers(text) :
    """ sig: (str) --> list int """
    nums = []
    for part in text.split(",") :
       nums.append(int(str.strip(part))) # possible ValueError
    return nums

def get_numbers(n) :
    text = input(f"enter {n} comma-separated numbers: ")
    return parse_numbers(text)    # possible ValueError

def get_numbers(n) :
    while True :
        try :
            text = input(f"enter {n} comma-separated numbers: ")
            return parse_numbers(text)    # possible ValueError
        except ValueError :
            print(f"I couldn't understand '{text}'")

def get_numbers(n) :
    while True :
        try :
            text = input(f"enter {n} comma-separated numbers: ")
            numbers = parse_numbers(text)  # possible ValueError
            if len(numbers) != n :
                raise ValueError("Wrong number of numbers!") # possible ValueError
            return numbers
        except ValueError:
            print(f"'{text}' is not {n} numbers")

def get_numbers(n) :
    while True :
        try :
            text = input(f"enter {n} comma-separated numbers: ")
            numbers = parse_numbers(text)  # possible ValueError
            assert len(numbers) == n , "Wrong number of numbers!" # possible AssertionError
            return numbers
        except (ValueError , AssertionError) :
            print(f"'{text}' is not {n} numbers")

def get_numbers(n) :
    while True :
        try :
            text = input(f"enter {n} comma-separated numbers: ")
            numbers = parse_numbers(text) # possible ValueError
            assert len(numbers) == n , "Wrong number of numbers!" # possible AssertionError
            return numbers
        except ValueError :
            print(f"I couldn't understand '{text}'")
        except AssertionError as err :
            print(err)

def get_num_between(low , high) :
    '''
    sig : (int , int) --> int
    prompts the user for a number between low and high.
    '''
    while True :
        try :
            text = input(f"enter a number between {low} and {high}: ")
            num = int(text) # possible ValueError
            assert low <= num and num <= high , \
                   f"{num} is not between {low} and {high}" # possible AssertionError
            return num
        except ValueError :
            print(f"I couldn't understand '{text}'")
        except AssertionError as err :
            print(err)

def leap_year(y) :
     return (y%4 == 0 and y%100 != 0) or y%400 == 0

def test_leap_year() :
   assert leap_year(2000) and not leap_year(1900) \
   and leap_year(2024) and not leap_year(2023)
