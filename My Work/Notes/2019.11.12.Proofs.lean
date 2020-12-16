/-
There are two key things we do with proofs.

(1) We build them
(2) We use them

In logic, the basic rules for building,
or constructing, proofs go by the name
of introduction rules. The basic rules
for using proofs are called elimination
rules.

Each *form* of proposition has its own
introduction and elimination rules. For
example, to build a proof of P ∧ Q, one
must use the introduction rule for and,
while using a proof of P ∧ Q relies on
the two elimination rules, which serve
to extract from a proof of P ∧ Q a proof
of P or a proof of Q.

In this class, we assume (P Q : Prop), 
(T : Type), (x y : T) then summarize, 
review,  and practice using the rules 
to build and use proofs of these forms:

- ∀ (p : P), Q [Q usually a predicate] -- intro rule for all - for all; Q - what form of prop and continue

- x = y -- intro rule : eq.refl 
- P → Q 
- P ∧ Q -- and.intro 
- ∃ (x : P), Q  [Q usually a predicate]

A key to understanding how to build
proofs is that it's a top-down and
recursive process. For example, to
build a proof of ∀ (p : P), Q, we
use the introduction rule for ∀. It
tells us to assume that p is some
arbitrary but specific value of type
P, and then to prove Q for that p.
To do this, we recursively apply 
our approach to building proofs to
build a proof of Q, but now within
a context in which we can use the
assumption that p is some specific
value of type P. We now repeat the
same process: (1) ask what form is 
Q; (2) choose an introduction rule
for that form of proposition. Often
we need smaller proofs to apply the
introduction rules, and for this, we
use proofs we have already built or
assumed, using elimination rules as
necessary.
-/

/-
FORALL INTRODUCTION

Assume that you have an arbitrary but specified valu of the quantiied type, ( p: P), then prove Q.

#0: Formalize Proposition 
∀ (b:Ball), Green b

#1: We start by assuming that b0 is an arbitrary but specific ball, and now all that remains to be proved is Green b (that this b in particular) is Green. 

Formally: Green b. Remaining goal. 

∀ (n:nat), n=n

Example: prove ∀ (n:nat), n=n.

#0 Assume that you have an arbitrary but specified valu of the quantiied type, (n:nat), then prove n=n.
#1 Use the introduction rule for equality 
#2: Need a proof of n

Proof: We begin by supposing that n0 is an arbitrary but specific natural number.  What remains to be proved in the context is that n0 = n0. [∀ intro]. To prove that n0 =n0 is trivial by the axiom that tells us that the equality relation id reflexive. Thus we have proved the propostion. [By reflexive property of equality.] 
-/

theorem foo : ∀ (n:nat), n=n :=
_

theorem all_n_eq_n : ∀ (n:nat), n=n :=
    λ (n0 : nat), eq.refl n0 
example : nat := 5

example : ∀ (n: nat) , nat.pred(nat.succ n) = n := 
λ (n0:nat), 
    eq.refl (nat.pred(nat.succ n0))


/-
FORALL ELIMINATION

-/

/-
Example:

Prove that is every ball is green, then a specific ball, b0, is green.

(∀ (b:Ball, Green b)) → ((b0: Ball) → (Green b0))

See below. Elim rule for fall is based that we can apply a proof of a forall to a specific value to build
-/


/-
IMPLICATIONS
INTRO FOR → 
Asume that we have a proof of the premise. 


Example : Prove
(∀ (b:Ball, Green b)) → ((b0: Ball) → (Green b0))

Introduction rule: assume the preduction is true 

Begin by assuming every ball is green, Must see nowwhether or not b0 is ball and is b0 is green. 

To prove this, we assume b0 is specific and inthis context all that remains to be proved is: b0 is green. this is proved by use of forall elimination. We apply our assumed* proof of (∀ (b:Ball, Green b)) → ((b0: Ball) → (Green b0)) to b) to obtain that b0 is green


-/
axioms (Ball: Type) (Green : Ball → Prop) 

example : (∀ (b:Ball), Green b) →  ∀ (b0: Ball), Green  b0 :=
λ h, 
    λ a,
        (h a)


/-
Assume that we have a proof, h, that every ball is green. In this context what remains to be proved is that any particular ball is green.

So now we assume that b0 is some arbitrary but specific ball, and inthis extend context of assumptions all that remains to be proved is that b0 is green. 

But we already have a proof that every bal is green so all we need to is apply it to b0 and that gives a proof that b0 is green. 

-/

/-

Build a syntax and evaluator for a language

Translate between props logic, predicate logic proofs etc. (Nobody likes anybody etc. )

Understand intro and elim rules for above props.
-/