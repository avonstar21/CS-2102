import .boxed
#check boxed 
open boxed 
def b2 : boxed nat := boxed.box 5 
def b3 := box 3

def b4 := boxed.box tt 

def b5 := boxed.box "I love polymorphism"

#check b3
#check b4
#check b5 

def unbox_poly {T: Type} : boxed T → T
| (boxed.box n) := n

#eval unbox_poly  b4
#eval unbox_poly  b5