variables (P Q R : Prop)

-- proof term
example: ∀  (P Q: Prop), ∀ (p : P), Q :=
    λ (p0: P),
        _

--proof script 
example: ∀ (P Q: Prop), ∀ (p:P), Q :=
begin
intros,
_
end

-- both of the above are the same

/-
FORALL ELIMINATION

-/
example :
    (∀ (p:P), Q) → 
    (P → Q):=
    λ h, 
        λ p,
            (h p)



example:
    (∀ (p:P), Q) →  -- arrows are right associative 
    P → 
    Q :=
λ (f : ∀ (p:P), Q), -- proof of ∀ 
    λ  (p:P),       -- proof of P
    (f p)              -- ∀ elimination 

/-
to show x ⇒ y

assume x, show y

a proof of this is a function from x → y.  
X is a parameter 
-/

example: P → Q → P ∧ Q :=

λ (p:P),
    λ (q: Q),
        and.intro p q 

example: (P ∧ Q) → P :=
λ (h: P ∧ Q), -- given proof of p ∧ q
    and.elim_left h -- return Q proof 

-- if you know 2 things are equal then you can make certain substitutions in the process  -> elimination or *rewrite*

axiom L: P → Prop -- assume some predicate L 

example : ∀ (a b:P), a = b → (L a → L b) :=
    λ a b, -- assume a and b are values of P
    λ heq, -- assume a proof of a = b
    λ la, -- assume a proof of (L a)
    (eq.subst heq la)  -- deduce proof of (L b)

example : P ∧ Q → Q ∧ P :=
λ (pq : P ∧ Q), -- assume proof P ∧ Q
    and.intro       -- apply and.intro
        pq.right  -- proof of Q
        pq.left     -- proof of P 

/-
what does it mean to say ¬ P?
¬ p is true when there are no proofs of P,

Meet "false". - a proposition itself which is never true

a proposition with no proofs

it is literally an empty type.
a type with no values

inductive false: Prop 
-/

#check false 

def f: false → 0 = 1
| p := false.elim p 

/-
¬ P === P → false 
-/