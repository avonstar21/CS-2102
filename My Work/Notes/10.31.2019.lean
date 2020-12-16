/-
Proofs:
- very structured, logical

Propositions can formalized as types and proofs are values of those types.
To Prove a Proposition : We assert there is a value at play. 
-/
-- review: we define day to be a type. [Computation type when capital t in type : Type]
inductive day : Type
| mon
|tue
|wed 
|thu 
|fri 
|sat 
|sun

/-
Now we can define variables of this type.
-/
open day
def l: day := _ -- hole : placeholder, := - turnstyle
def d: day := 
begin
    --sccripting terms
    exact tue,  -- exact must give value which is required by goal
end

/-
emily_from_cville
-/

inductive emily_from_cville: Prop -- logical type, not computational
/-
Constructors define the values, which we now accept as proofs of the proposition. Proofs in lean are values of *logical* types. 
-/
| drivers_license
| passport
| utility_bill

inductive empty_data_type : Type
inductive myfalse : Prop 

open emily_from_cville 

def a_proof : emily_from_cville := _ 
-- waiting for a constructor

def a_proof': emily_from_cville :=
begin
    exact utility_bill, 
end

theorem a_proof'' : emily_from_cville := 
begin
    exact passport
end

inductive person :Type
|mari
|jose
|jane
|bill 

open person 
-- proposition with a parameter is a predicate 

-- is_from_cville is a predicate 
-- a predicate can be thought of defining a property of the parameter to which it applies. 

inductive is_from_cville : person → Prop 
|proof_for:
    ∀ (p: person)
        p = mari → is_from_cville mari 

open is_from_cville 
#check is_from_cville mari
#check is_from_cville jose 
#check is_from_cville jane
#check is_from_cville bill  

#check proof_for mari  -- proof for is a constructor, all that is required is that mari == mari

theorem mari_is_from_cville : is_from_cville mari :=
begin 
    --scripting command
    apply proof_for _  _,
    --proof for is a constructor, given any person p that if you can prove p = mari, then you have a proof that mari is from cville. 
    exact mari,
    exact (eq.refl mari),   
end  

theorem jose_is_from_cville : is_from_cville jose :=
begin 
    --scripting command
    apply proof_for _  _,
    --proof for is a constructor, given any person p that if you can prove p = mari, then you have a proof that mari is from cville. 
    exact jose,
    exact (eq.refl jose),   
end
 -- equality is just a predicate 
 /-
 eq     a           b

 is the same as

 a = b

 eq     1       3
 1 = 3 - a false proposition, but a proposition nevertheless

 eq 1   1
 1 = 1

 eq is a proof constructor where there is an inductive def of eq which is nat → nat → prop where | refl ℕ → eq n n

 equality as a binary relation is reflexive

 relation : a set of pairs 

 Symetry : if a,b is in, then so is b,a 

 equality is symetric and reflexive 

 Property of relations:

 Binary relation is transitive if a likes b, b likes c then a likes c.

 
 -/

 def evenb (n : nat) : bool :=
    n %2 = 0 -- computational predicate yields a bool. Logical predicate yields a proposition. 

inductive is_zero : ℕ → Prop 
| zmk : ∀ (n:ℕ ), n = 0 → is_zero n 

open is_zero 


