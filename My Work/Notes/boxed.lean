inductive boxed_nat : Type
| box : nat → boxed_nat

open boxed_nat

def b1: boxed_nat := box 3

#check b1
#reduce b1 

-- take bozed_nat and return the nat. Call it unbox.

def unbox : boxed_nat → nat
| (box n) := n

#reduce unbox b1 

/-
Creating A simple polymorphic data type :-
-/

inductive boxed (T : Type) : Type
| box : T → boxed -- does not require boxed T because lean knows what ur doing 

-- lean has type inference
-- it can synthesize that value

-- to create inference use curly brackets instead of parentheses
