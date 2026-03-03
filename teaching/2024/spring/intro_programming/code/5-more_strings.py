# script file from lecture on 2024-02-02

def rotate(num , text) :
    '''
    signature : (int , str) --> str
    Rotate the first num characters in the string to the end.
    '''
    first = text[ : num]
    last = text[num : ]
    return last + first

# or
def rotate(num , text) :
    return text[num : ] + text[ : num]

def fav_book() :
    # ask the user their fav book
    answer = input('What is your favorite book? ')
    # clean up their answer
    title = str.title(str.strip(answer))
    # print that it's your fav book too
    print('What a coincedence, "' + title +
          "\" is my favorite book too!")
