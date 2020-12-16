/-
Terms
-/

/-
Literal Terms
-/


#eval 1
#eval 77

#check 77

#check nat
#check ℕ

#check bool 
#check tt /-true-/
#check ff /-false-/

#eval tt

#eval "Hello, Lean!"

#eval "Whomp there it is!"


/-
Identifier terms: a name for another term
-/

def n := 1

/-def n := 2 cannot exist as no mutable storage!-/

#check n
#eval n
--evaluating an identifier retruns the value the identifier is bound too. 

def m : ℕ := 1
def k :  ℕ := "Hello"

#check k
/-#eval k will not work because type mismatch -/

def j: ℕ := 3


/-
Function  Types
-/

#check bool → bool --unary
#check bool → bool → bool --binary
-- And function, Or function
#check nat → nat  --unary
#check nat → nat → nat --binary
#check nat → (nat → nat) -- arrow is right associative

-- the above expression is dealing with partial evaluation

#check (nat → nat) → nat -- accepts function as argument which returns a natural number

/-
Function Values
-/

-- function that takes 1 bool and retruns 1 bool

def always_false : bool → bool :=
    λ b:bool, ff

def always_true : bool → bool:=
    λ g:bool, tt 

def identity_func : bool → bool :=
    λ i:bool, i

def test_func : nat → bool :=
    λ j:nat, tt 

def increment : nat → nat :=
    λ n: ℕ, n + 1

#eval (λ n: ℕ, n + 1) 6

#check (λ n, n+1 ) 6
#eval(λ n, n+1 ) 6

def add_num : nat → (nat → nat):=
    λ m:nat,
        λ l:nat, l + m 

#eval (add_num 2) 7

def incby5 := add_num 5

#eval incby5 4
#eval incby5 22

#eval add_num 11 15

/-we used lambda abstractions to implement functions-/
def neg_bool : bool → bool :=
    λ b: bool,
        match b with
        | tt := ff
        | ff := tt
        end

#eval neg_bool tt
#eval neg_bool ff
#eval neg_bool (neg_bool ff)
#eval neg_bool (neg_bool tt)

def neg_bool' : bool → bool 
   | tt := ff
   | ff := tt

def xor2 : bool → bool → bool :=
|tt tt := tt
|tt ff := tt
|ff tt := tt
|ff ff := ff

def xor' : bool → bool → bool :=
λ b1 : bool,
    λ b2: bool,
        match b1, b2 with
            | tt, tt := tt
            | tt, ff := tt
            | ff, tt := tt
            | ff, ff := ff  
        end 