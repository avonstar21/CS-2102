/-
• Show and Tell by dude named Jason to boost his ego. 
-/

/-
Introducing 
True and False
-/

#check true 
#check false

inductive True : Prop 
| True.intro : true

/-
java's void is same as Lean's empty
-/

#check empty -- no constructors 

/-
False is the empty or uninhabited type. There are no proofs of it, so it is not true
-/

#check unit 
#print unit -- #print prints the type to lean messages. 

theorem trueisTrue : true := true.intro -- proof of true

theorem falseIsTrue : false := _ -- can't finish this, why? no proof of false

def falseImpliesCrazy (f: false) : 0 = 1 := 
false.elim f 
-- if false is true, then everything and anything is true

example : false → 0 = 1  :=
λ (f :false),
    false.elim f

example : ∀ (P:Prop), false → P :=
λ (P : Prop),
    λ (f : false),
        false.elim f 

def x : bool → bool 
| tt := _ 
| ff := _ 

def y: unit → bool
| punit := _ 

def z: false → bool
| (f:false) := false.elim f

/-
defining not operator
-/

#print not -- defined as a function that takes prop a and returns a → false

axiom P : Prop 

#check ¬ P 
#reduce ¬ P -- not P simply means P → false 

/-
if not p is true, that is saying that it is true that p → false. this means there is a proof of this implication. a proof of an implication is a function that takes an argument of type P → false . 
-/
/-
Proof by negation: 
-/

example: ¬ P := 
λ (p : P),
    _ 

example: P → ¬ P → false := 
λ (p:P),
    λ (np : ¬ P),
        (np p) 

example: P → ¬ P → false := 
begin
    assume (p : P),
    assume (np : P → false),
    exact (np p),
end  

/-
If p is true and if not p is true then false is true. (Prove this)

Assumpe P is true and that ¬ P is also true and show that false is true. Apply ¬P to P to get false. QED.
-/

example: P → ¬ P → 0 = 1 := 
begin
assume (p : P),
assume (np : ¬ P),
exact false.elim (np p),
end

axiom Q : Prop 

axiom q : Q

example : P ∨ Q := 
or.inr q 


axiom em: ∀ (P : Prop), P ∨ ¬ P

example : P ∨ ¬ P :=
em P 

example : Q ∨ ¬ Q :=
em Q 

example : P ∨ Q → (P → R) → (Q → R) → R :=
_ 