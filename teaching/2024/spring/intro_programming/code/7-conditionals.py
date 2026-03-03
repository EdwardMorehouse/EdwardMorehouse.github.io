# script file from lecture on 2024-02-08

def fav_subject() :
    fav = input("What's your favorite subject? ")
    if str.lower(fav) == "computer science" :
        print("That's my favorite too!")
    print(str.title(fav) + " is a great subject.")

def guessing_game () :
    print("Think of a thing.")
    if input("Is it an animal? ") == "yes" :
        print("Then it must be a capybara")
    elif input("Is it a vegetable? ") == "yes" :
        print("Then it must be kale")
    elif input("Is it a mineral? ") == "yes" :
        print("Then it must be pyrite")

def cs_survey() :
    response = str.lower(input("Do you like C.S.? "))
    if response == "yes" :
        print("I know, right?!")
    elif response == "no" :
        print("I'm sorry to hear that you feel that way.")
    else :
        print("I'm sorry, I didn't understand that.")
    
def leap_deep(y) :
    if y%4 == 0 :
        if y%100 == 0 :
            if y%400 == 0 :
                print(str(y) + " is a leap year")
            else :
                print(str(y) + " is not a leap year")
        else :
            print(str(y) + " is a leap year")
    else:
        print(str(y) + " is not a leap year")

def leap_flat(y) :
    if (y % 4 == 0 and y % 100 != 0) or y % 400 == 0 :
        print (str(y) + " is a leap year")
    else :
        print (str(y) + " is not a leap year")

def what_to_do(day) :
    d = str.lower(day)
    if d == "sunday" or d == "monday" or d == "tuesday" :
        return "study"
    elif d == "thursday" or d == "friday" or d == "saturday" :
        return "party"
    else :
        return "dunno"

def number_size() :
    number = int(input("Please enter a number: "))
    size = "small" if number < 10 else "big"
    print("That's pretty " + size)
