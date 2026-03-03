# script file from lecture on 2024-04-23

import turtle

class Shape :

    def __init__(self , position , size , color) :
        self.position = position
        self.size = size
        self.color = color
        self.angle = 0                  # new
        self.line_width = 1             # new

    def set_angle(self , angle) :       # new
        self.angle = angle              # new

    def set_line_width(self , width) :  # new
        self.line_width = width         # new

    def draw(self) :
        turtle.penup()
        turtle.goto(self.position)
        turtle.setheading(self.angle)   # new
        turtle.pencolor(self.color)
        turtle.pensize(self.line_width) # new
        turtle.pendown()
        # nothing to draw yet


class Circle(Shape) :

    # inherits __init__

    def draw(self) :    #  Circle.draw overrides Shape.draw
        super().draw()  #  calls Shape.draw(self)
        turtle.circle(self.size)


class Square(Shape) :

    # inherits __init__
    def draw(self) :
        super().draw()
        for _ in range(4) :
            turtle.forward(self.size)
            turtle.left(90)


class Polygon(Shape) :

    # override the initializer with an additional argument:
    def __init__(self , sides , position , size , color) :
        self.sides = sides
        super().__init__(position , size , color)

    # override the draw method to draw a polygon:
    def draw(self) :
        super().draw()
        for _ in range(self.sides) :
            turtle.forward(self.size)
            turtle.left(360/self.sides)


class Triangle(Polygon) :

    def __init__(self , position , size , color) :
        super().__init__(3 , position , size , color)


class Square(Polygon) :
    def __init__(self , position , size , color) :
        super().__init__(4 , position , size , color)


