namespace prop_logic

/-SYNTAX-/

inductive var : Type
| mkVar : ℕ → var

inductive unOp : Type
|notOp

inductive binOp : Type
| andOp
| orOp

inductive pExp: Type
| litExp: bool → pExp 
| varExp: var → pExp 
| unOpExp : unOp → pExp → pExp 
| binOpExp : binOp → pExp → pExp → pExp

def pTrue := pExp.litExp true 

open var
open pExp
open unOp 
open binOp  

def pAnd := binOpExp andOp
def pOr := binOpExp orOp
def pNot := unOpExp notOp 

-- conventional notation

notation e1 ∧ e2 := pAnd e1 e2
notation e1 ∨ e2 := pOr  e1 e2
notation ¬ e1 := pNot e1