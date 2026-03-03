# script file from lecture on 2024-02-23

def reverse_list(items) :
    acc = []
    for item in items :
        acc = [item] + acc
    return acc

def deduplicate(items) :
    acc = []
    for item in items :
        if item not in acc :
            acc = acc + [item]
            # or
            #acc.append(item)
    return acc

def map_even(nums) :
    results = []
    for num in nums :
        results.append(num % 2 == 0)
    return results

def reverse_word(text) :
    #strategy:
    # 1: listify the string
    letter_list = list(text)
    # 2: reverse the list
    reversed_list = reversed(letter_list)
    # 3: stringify the list
    return str.join('' , reversed_list)

def reverse_word(text) :
    return ''.join(reversed(list(text)))

def reverse_words(sentence) :
    words = sentence.split()
    # map reverse_word over words
    acc = []
    for word in words :
        acc.append(reverse_word(word))
    # combine the list of words back to a sentence
    return ' '.join(acc)

def filter_even(nums) :
    evens = []
    for num in nums :
        if num % 2 == 0 :
            evens.append(num)
    return evens
    
def remove_vowels(text) :
    acc = []
    for letter in list(text) :
        if letter.lower() not in ['a', 'e', 'i', 'o', 'u'] :
            acc.append(letter)
    return ''.join(acc)



