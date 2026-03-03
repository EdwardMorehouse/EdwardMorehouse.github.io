# script file from class on 2024-03-01

def prompt_num() :
    return input("please enter a number: ")

def get_num() :
    answer = ""
    while not answer.isdigit() :
        answer = input("please enter a number: ")
    return int(answer)

things = ['a balloon', 'candy', 'ice cream',
          'french fries', 'a pony']

import random

def gimme() :
    answer = 'no'
    while answer.lower() not in ['yes', 'okay', 'whatever'] :
        thing = random.choice(things)
        answer = input(f'Can I have {thing}? PLEASE? ')
    print(f'Yay! {thing}')

def pick() :
     return random.randint(1 , 10)

def guessing_game() :
    num = pick()
    print("I'm thinking of a number between 1 and 10.")
    print('Try to guess it!')
    guess = -1
    while guess != num :
        guess = get_num()
        if guess < num :
            print('too low, guess again!')
        elif guess > num :
            print('too high, guess again!')
    print(f"You got it, the number was {num}!")

def alternate_case(text) :
    result = ''
    i = 0
    while i < len(text) :
        letter = text[i]
        result += letter.upper() if i%2==0 else letter.lower()
        i += 1
    return result
