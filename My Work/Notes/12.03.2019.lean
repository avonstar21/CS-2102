/-
Proof Strategies:
Intro rules for or - 
or.inl takes a proof of P and returns a proof of P ∨ Q
or.inr takes a proof of Q  and returns a proof of P ∨ Q
or ⇒ disjuncture 
-/

axiom Q : Prop 
axiom P : Prop 
axiom q: Q 

example : P ∨ Q :=
or.inr q -- because no proof of P exists 

example : 0 = 1 ∨ 2 = 2 :=
or.inr (eq.refl 2)
--or.intro_right (0 = 1) rfl 

-- CONSTRUCTIVE LOGIC
example : P ∨ ¬ P :=
begin
-- yikes... 
-- apparently we are stuck 
-- no proof either way!
_ 
end

-- CLASSICAL LOGIC
-- law of the excluded middle
axiom em: ∀ (P : Prop), P ∨ ¬ P 
 #check em Q 

example : ∀ (P : Prop), ¬ (¬ P) → P := 
begin
assume P,
assume nnp, -- (P → false) → false
cases (em P) with p np ,
exact p,
--exact false.elim (nnp np),  -- constructively this doesn't have a proof.
contradiction, 
end 

axiom : ∀ (P : Prop), ¬ (¬ P) → P 

/-
proof by contradiction 
look up and add here the difference between proof by negation and proof by contradiction

- show P, prove ¬ ¬ P (¬ P → false)


proof by negation is used to prove a prop of the form ¬ P. this world whenever you try and use 
- show ¬ P, prove P → false

(PBC) if you want to show that P is true, assume it is false and show how that leads to a contradiction. 
-/

-- paper pencil proof of square root 2 is irrational 

/-
NEGATION                                        CONTRA
want ¬ P                                            want P,
show p → ff                                         show ¬ ¬ P
assume (p: P)                                       then infer P
show contradiction, proof of false                  → ¬ P → false
                                                [¬ ¬ P → P, classically valid]
-/

/-
40% of the exam is actually about the functional programming we have learned.
60% is propositions and proofs. (intro rules and elimination rules)
-/ 

axioms 
    (R : Prop)
    (p : P)
    (pr: P → R)
    (qr: Q → R)

example : (P ∨ Q) → R :=
λ (pq : P ∨ Q),
match pq with 
| or.inl pfP := pr p 
| or.inr pfQ := qr q
end 

