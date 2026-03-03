# script file from lecture on 2024-02-09

import turtle

def draw_square(size) :
     turtle.forward(size)
     turtle.left(90)
     turtle.forward(size)
     turtle.left(90)
     turtle.forward(size)
     turtle.left(90)
     turtle.forward(size)
     turtle.left(90)
 
def draw_rectangle(height) :
    # width is twice the height
    turtle.forward(2 * height)
    turtle.left(90)
    turtle.forward(height)
    turtle.left(90)
    turtle.forward(2 * height)
    turtle.left(90)
    turtle.forward(height)
    turtle.left(90)

def draw_scalable_rectangle(width , height) :
    turtle.forward(width)
    turtle.left(90)
    turtle.forward(height)
    turtle.left(90)
    turtle.forward(width)
    turtle.left(90)
    turtle.forward(height)
    turtle.left(90)
