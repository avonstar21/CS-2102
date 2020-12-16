/-
pEval e i

pEval : pExp → (var → bool) → bool
e: propositional logic statement 
    an exoression is valid if every interpretation is a model
    satisfiable if only some interpretation is a model
    unsatisfiable if no interpretation is a model
i: interpretation → i is a 'model' of e if it makes it true
-/ 

def isModel (i: var → bool) (p: pExp) :=
    pEval e i = tt

def valid (e: pExp) :=
    ∀ (i: var → bool),
     isModel i e 

def unsatisfiable (e: pExp) :=
    ∀ (i: var → bool),
        ¬ isModel i e

def unsatisfiable' (e: pExp) :=
    ¬ ∃ (i: var → bool),
         isModel i e

def satisfiable (e : pExp) :=
    ∃(i : var → bool),
        isModel i e 

def satisfiable' (e : pExp) :=
    ∃(i : var → bool),
        isModel i e 

-- each row of truth table is an interpretation. 

/-
3 Steos of constructing a proof of P ∧ Q: 
expression
spatisfiable 
not valid 

Inference rules: 
if p is true it is predicate logic and correct
 
False always implies true, must look at truth table for implies
(r → w) → (¬ r → ¬ w)
R   W  ¬ R   ¬ W  (R→ W) (¬ R → ¬W)  (r → w) → (¬ r → ¬ w)
T   T   F       F   T           T         T         T   
-/

/-
Standard Valid Inference Rules:
P : T T F F
Q : T F T F
(P → (Q → P ∧ Q)) : T T T T -- and introduction
-/


def and_elim_left := P ∧ Q → P 
def and_elim_right := P ∧ Q → Q 
-- def or_intro_left := P ∨ Q → (either p or q is true if known is enough)
def or_intro_left := P →   P ∨ Q
def or_intro_right := Q →   P ∨ Q