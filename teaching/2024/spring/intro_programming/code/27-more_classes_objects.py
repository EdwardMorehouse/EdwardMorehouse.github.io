# script file from lecture on 2024-04-12

import random, time, turtle

# some global variables:
dot_size = 10
timestep = 1/60
max_speed = 500

# from last time:
def init_turtle() :
    # don't show the turtle icon:
    turtle.hideturtle()
    # default turtle state is not drawing:
    turtle.penup()
    # don't render to screen unless instructed:
    turtle.tracer(0 , 0)

# two helper functions:
def reflect_x (pair) :
    ''' sig: (tuple [int , int]) --> tuple [int , int] '''
    (x , y) = pair
    return (-x , y)

def reflect_y (pair) :
    ''' sig: (tuple [int , int]) --> tuple [int , int] '''
    (x , y) = pair
    return (x , -y)


class Ball :
    ''' A class for simulating the motion of a ball's position and velocity '''
    def __init__(self , init_pos , init_vel) :
        ''' sig : (Ball , tuple [int , int] , tuple [int , int]) --> NoneType '''
        self.position = init_pos
        self.velocity = init_vel
    
    def __str__(self) :
        ''' sig: (Ball) --> str '''
        return f"Ball p:{self.position} v:{self.velocity}"
    
    def __repr__(self) :
        ''' sig: (Ball) --> str '''
        return str(self)
    
    def get_pos(self) :
        ''' sig: (Ball) --> tuple [int , int] '''
        return self.position
    
    def get_vel(self) :
        ''' sig: (Ball) --> tuple [int , int] '''
        return self.velocity
    
    def move(self , time) :
        ''' sig: (Ball , int) --> NoneType
            update the ball's state based on how much time has passed '''
        (p_x , p_y) = self.position
        if abs(p_x) >= 250 :
            self.velocity = reflect_x(self.velocity)
        if abs(p_y) >= 250 :
            self.velocity = reflect_y(self.velocity)
        (v_x , v_y) = self.velocity
        self.position = (p_x+(v_x*time) , p_y+(v_y*time))


# a set of balls:
balls = set()

# add a random ball to the set:
def add_ball() :
    x_vel = random.randint(-max_speed , max_speed)
    y_vel = random.randint(-max_speed , max_speed)
    new_ball = Ball((0 , 0) , (x_vel , y_vel))
    balls.add(new_ball)

# draw a single ball:
def draw_ball(ball) :
    ''' sig: (Ball) --> NoneType '''
    (x , y) = ball.get_pos()
    turtle.goto(x , y)
    turtle.dot(dot_size)

# function to run the ball simulator animation:
def run_balls() :
    init_turtle()
    turtle.onkeypress(add_ball , 'space')
    turtle.listen()
    while True :
        turtle.clear()
        for ball in balls :
            draw_ball(ball)
            ball.move(timestep)
        turtle.update()
        time.sleep(timestep)


