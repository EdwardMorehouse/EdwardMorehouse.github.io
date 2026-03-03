# script file from lecture on 2024-04-11

import turtle

def init_turtle() :
    # don't show the turtle icon:
    turtle.hideturtle()
    # default turtle state is not drawing:
    turtle.penup()
    # don't render to screen unless instructed:
    turtle.tracer(0 , 0)

dot_size = 10

def dot_at(coords) :
    (x , y) = coords
    turtle.goto(x , y)
    turtle.dot(dot_size)

dot_pos = (0 , 0)

def draw_dot() :
    init_turtle()
    dot_at(dot_pos)

class Point : # class header
    def __init__(self , init_x , init_y) :
        ''' sig: (Point , int , int) --> NoneType'''
        self.x = init_x
        self.y = init_y
    
    def set_pos(self , position) :
         ''' (Point , tuple (int , int)) --> NoneType '''
         (self.x , self.y) = position
    
    def get_pos(self) :
         ''' (Point) --> tuple (int , int) '''
         return (self.x , self.y)
    
    def move_right(self) :
         ''' (Point) --> NoneType '''
         self.x += 10

# a new Point object:
my_point = Point(0 , 0)

# a callback function to move the dot:
def move_dot_right() :
    turtle.clear()  # erase old scene
    my_point.move_right()
    dot_at(my_point.get_pos())
    turtle.update() # paint new scene

# set up turtle to respond to events:
def run_dot () :
    init_turtle()
    dot_at(my_point.get_pos())
    turtle.onkeypress(move_dot_right , 'Right')
    turtle.listen()

