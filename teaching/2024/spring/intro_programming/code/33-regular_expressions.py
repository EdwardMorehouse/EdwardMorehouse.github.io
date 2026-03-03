# script file from class on 2024-04-26

import re

just_cat = 'cat'  # represents the set {'cat'}
just_hat = 'hat'  # represents the set {'hat'}
cat_or_hat = 'cat|hat' # represents the set {'cat', 'hat'}

digit = '0|1|2|3|4|5|6|7|8|9'
digit = '[0123456789]' # a character class for digits
not_digit = '[^0123456789]'   # a class for non-digits

letter = '[a-zA-Z]'

number = r'\d+'  # one or more consecutive digits

word = '[a-zA-Z]+'
word = letter + '+'

three_digit_number = r'\d{3}'
three_or_four_digit_number = r'\d{3,4}'

color = 'colou{0,1}r'
colour = 'colou?r'

only_number = r'^\d+$'

telephone = r'\(\d{3}\)\d{3}-\d{4}'

