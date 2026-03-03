# script file from class on 2024-05-07

# summing positive numbers in a list
# sig: (list int) --> int

# by loop iteration:
def sum_pos(nums) :
    acc = 0
    for num in nums :
        if num > 0 :
            acc += num
    return acc

# by recursion:
def sum_pos(nums) :
    if nums == [] :
        return 0  # base case
    else :
        rec = sum_pos(nums[1: ])  # recursive call
        if nums[0] > 0 :           # try shortening this part
            return nums[0] + rec
        else :
            return rec

# by higher-order functions:
def sum_pos(nums) :
    return sum(filter(lambda num : num > 0 , nums))


# Lamp class
class Lamp :
    def __init__(self , name) :
        self.name = name
        self.state = False
    
    def __str__(self) :
        return f' Lamp {self.name}, which is {"on" if self.state else "off"}'
    
    def toggle(self) :
        self.state = not self.state


