import .prop_logic
open prop_logic 
open prop_logic.var
open prop_logic.var
open prop_logic.pExp 
open prop_logic.unOp 
open prop_logic.binOp

def varX := mkVar 0
def varY := mkVar 1
def varZ:= mkVar 2

#check pExp.litExp ff
#eval pExp.litExp ff 

def X : pExp := varExp varX
def Y : pExp := varExp varY
def Z : pExp := varExp varZ 
#check X
#check Y 

#check unOpExp notOp pTrue
#check unOpExp notOp 