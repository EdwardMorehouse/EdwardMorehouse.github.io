# script file from class on 2024-03-08

def file_read(path) :
    """ (str) --> str """
    with open(path) as file :
        contents = file.read()
        # no close necessary
    return contents

# data : list (tuple [str, str, float])
data = \
[  #  name          ,  diet          , weight
    ('Whiskers'     , 'rat chow'     , 300.0) ,
    ('Mr. Squeeky'  , 'swiss cheese' , 450.0) ,
    ('Pinky'        , 'rat chow'     , 320.0) ,
    ('Fluffball'    , 'swiss cheese' , 500.0)
]

import csv

def load_csv(path) :
    ''' sig: (str) --> list (list str) '''
    data = []         # accumulator to store file contents
    with open(path , 'r') as file : # open a file for reading
        reader = csv.reader(file) # create a csv reader
        for row in reader : # iterate over CSV reader
            data.append(row)
    return data

csv_data = load_csv('diets.csv')

diets_header = csv_data[0]

def parse_row(parsers , cells) :
    ''' sig: (list fun , list str) --> tuple '''
    results = ()  # the empty tuple with type tuple []
    for (parser, cell) in zip(parsers, cells, strict=True) :
        parsed_cell = parser(cell) # parse the cell
        # concatenate a *singleton tuple* to the results:
        results += (parsed_cell , )
    return results

def parse_table(parsers , rows) :
    ''' (list fun , list (list str)) --> list tuple '''
    # the `map` pattern:
    acc = []
    for cells in rows :
        acc.append(parse_row(parsers , cells))
    return acc

diets = parse_table([str,str,float] , csv_data[1:])

diets.append(('Ricky' , 'rat chow' , 280.0))

def store_csv(path , headers , data) :
    with open(path , 'w' , newline='') as file :
        writer = csv.writer(file) # create a csv writer
        writer.writerow(headers)  # write the header row
        writer.writerows(data)    # write the table rows

