import .prop_logic 
import .bool_sat

open prop_logic 
open prop_logic.var
open prop_logic.pExp


/-
An example: The 0th, 1st, and 
2nd bits from the right in 100, 
the binary numeral for decimal
4, are 0, 0, and 1, respectively.
-/
#eval mth_bit_from_right_in_n 2 4

/-
#1. Write and evaluate expressions
(using eval) to determine what is 
the bit in the 9th position from
the right in the binary expansion
of the decimal number 8485672345? 

Hint: don't use reduce here. Eval
uses hardware (machine) int values
to represent nats, while reduce 
uses the unary nat representation. 

Self-test: How much memory might 
it take to represent the decimal
number, 8485672345, as a ℕ value
in unary? -- come back here
-/

#eval mth_bit_from_right_in_n 9 8485672345


/-
The next section presents examples
to set up test cases for definitions
to follow.
-/

/-
We define a few variables to use
in the rest of this assignment.
-/
def P : pExp:= varExp (mkVar 0)
def Q: pExp := varExp (mkVar 1)
def R : pExp := varExp (mkVar 2)

/-
We set parameter values used in
some function definitions to follow.
-/
def max_var_index := 2
def num_vars := max_var_index + 1

/-
An example of a propositional logic
expression.
-/
def theExpr : pExp := (pImpl P (P ∧ R))


/-
An example using the truth_table_results
function to compute and return a list of 
the truth values of theExpr under each of 
its possible interpretations.
-/
#eval truth_table_results theExpr num_vars


/-
#2. Define interp5 to be the interpretation
in the six row (m=5) of the truth table that
our interps_for_n_vars functions returns for
our three variables (P, Q, and R). 

Hint: use the mth_interp_n_vars function.
Definitely check out the definition of the
function, and any specification text, even 
if informal, given with the formal definition.
-/
#eval interps_for_n_vars 3
#eval truth_table_results P
def interp5 := mth_interp_n_vars 5 3 

/-
#3. What Boolean values are assigned to 
P, Q, and R by this interpretation (interp5)? 
Use three #eval commands to compute answers by 
evaluating each variable expressions under the
interp5 interpretation.
-/

#eval interp5 (mkVar 0) -- P
#eval interp5 (mkVar 1) -- Q
#eval interp5 (mkVar 2) -- R



/-
#4. Write a truth table within this
comment block showing the values for
P, Q, and R, in each row in the truth
table, represented by a corresponding
value in the list of interpretations
returned by interps_for_n_vars. Label
your columns as R, Q, and P, in that
order. (Try to understand why.) 
Hint: Don't just write what you think
the answers are:, evaluate each of
the three variable expression under
each interpretation. You can use the
mth_interp_n_vars function if you want
to obtain interpretation functions for
each of the rows individually if you
want. 


Answer: 
    R   |   Q   |   P  
  ----------------------
    F       F       F      
    F       F       T      
    F       T       F      
    F       T       T      
    T       F       F      
    T       F       T      
    T       T       F      
    T       T       T      
-/


/-
#5. Write an expression here to
compute the "results" column of
the truth table for "theExpr" as
defined above.
-/

#eval truth_table_results theExpr

/-
#6. Copy and paste the truth table
from question #4 here and extend it
with the results you just obtained.
Check the results for correctness.

Answer here:

    R   |   Q   |   P   | TheExpr
  --------------------------------
    F       F       F       T
    F       F       T       T
    F       T       F       T
    F       T       T       T
    T       F       F       F
    T       F       T       T
    T       T       F       F
    T       T       T       T


-/

/-
#7.

Write a "predicate" function, isModel,
that takes a propositional logic 
expression, e, and an interpretation, 
i, as its arguments and that returns 
the Boolean true (tt) value if and only
if i is a model of e (otherwise false).
-/

def isModel :pExp → (var → bool) → bool
| pExp f := if ∀ (b : truth_table_results pExp f) then tt else ff


/-
#8. Write a one-line implementation
of a function, is_valid, that takes as
its arguments a propositional expression, 
e, and the number of variables, n, in its
truth table, and that returns true if and
only if it is valid, construed to mean
tha every result in the list returned by 
the truth_table_results function is true.

To do so, define and use a fold function
to reduce returned lists of Boolean truth
values to single truth values. Define and
use a bool-specific function, fold_bool :
    (bool → bool → bool) - binary operator
     → 
    bool - identity element for that operator 
    → 
    (list bool) - list to be reduced
    
     → 
    bool,
where the arguments are, respectively, 
a binary operator, an identity element
for that operator, and a list of bools
to be reduced to a single bool result. 
-/

def fold_bool :
    (bool → bool → bool) → bool → (list bool) → bool
| func id [] := id
| func id (list.cons (h) (t)) :=  func h ( fold_bool func id t )
 
#eval fold_bool band tt [tt,ff,tt]

def is_valid : pExp → ℕ → bool
|pExp num_vars := fold_bool band tt (truth_table_results pExp num_vars) 

/-
Write similar one-line implementations of the
functions, is_satisfiable and is_unsatisfiable, 
respectively. Do not use fold (directly) in your 
implementation of is_unsatisfiable.
-/

def is_satisfiable : pExp → ℕ → bool
|pExp num_vars := if fold_bool bor ff (truth_table_results pExp num_vars) 
  then tt
  else ff 


def is_unsatisfiable : pExp → ℕ → bool
|pExp num_vars := if fold_bool bor ff (truth_table_results pExp num_vars) 
  then ff
  else tt

/-
9. Use your is_valid function to determine which
of the following putative valid laws of reasoning
really are valid, and which ones are not. For each
one that is not, give a real-world scenario that
shows that the rule doesn't always lead to a valid
deduction. Use #eval to evaluate the validity of 
each proposition. Use -- to put a comment after
each of the following definitions indicating
either "-- valid" or "-- NOT valid".
-/

def true_intro : pExp := pTrue -- valid
#eval is_valid true_intro 3
def false_elim := pImpl pFalse P -- valid
#eval is_valid false_elim 3
def and_intro := pImpl P (pImpl Q (P ∧ Q)) -- valid
#eval is_valid and_intro 3   
def and_elim_left := pImpl (P ∧ Q) P  -- valid
#eval is_valid and_elim_left 3 
def and_elim_right := pImpl (P ∧ Q) Q  
#eval is_valid and_elim_right 3
def or_intro_left := pImpl P (P ∨ Q)
def or_intro_right := pImpl Q (P ∨ Q)
def or_elim := pImpl ( P ∨ Q) (pImpl (pImpl P R)  (pImpl (pImpl Q R)  R))
def iff_intro := pImpl (pImpl P Q) (pImpl(pImpl Q  P) (P ↔ Q))
def iff_elim_left := pImpl (P ↔ Q) (pImpl P Q)
def iff_elim_right := pImpl (P ↔ Q) (pImpl Q  P)
def arrow_elim := (pImpl P  Q) ( pImpl ( pImpl P  Q))
def affirm_consequence := (P ⇒ Q) ⇒ Q ⇒ P
def resolution := (P ∨ Q) ⇒ (¬ Q ∨ R) ⇒ (P ∨ R)
def unit_resolution := (P ∨ Q) ⇒ (¬ Q) ⇒ P
def syllogism := (P ⇒ Q) ⇒ (Q ⇒ R) ⇒ (P ⇒ R)
def modus_tollens := (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
def neg_elim := ¬ ¬ P ⇒ P
def excluded_middle := P ∨ ¬ P
def neg_intro := (P ⇒ pFalse) ⇒ ¬ P
def affirm_disjunct := (P ∨ Q) ⇒ P ⇒ ¬ Q
def deny_antecedent := (P ⇒ Q) ⇒ (¬ P ⇒ ¬ Q)

-- Answer below
