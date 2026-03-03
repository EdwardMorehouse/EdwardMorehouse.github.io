# script file from class on 2024-04-25

class Square :

    sides = 4           # a static attribute

    @staticmethod       # static method decorator
    def get_sides() :   # a static method
        return Square.sides   # refers to a static attribute

    def __init__(self , size) :
        self.size = size

    def perimeter(self) :
        return Square.sides * self.size

