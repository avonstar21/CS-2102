/-
Nat Language PRopositie

example: if there is somone everyone likes, thne everyone likkes someone. 
-/
axiom Person: Type
axiom Likes: Person → Person → Prop


example: (∃ (p : Person), ∀ (q : Person), Likes q p ) → ( ∀ (p:Person), ∃ (q : Person), Likes p q ) :=
begin
assume h, 
assume p,
cases h with w pf,
apply exists.intro w pf,
exact (pf p)
end 

/-
Witness: proof that the witness has the given property. 
-/

example: (∃ (p : Person), ∀ (q : Person), Likes q p ) → ( ∀ (p:Person), ∃ (q : Person), Likes p q ) :=
begin
assume h,
assume p,
cases h with w pf,
apply exists.intro w pf,
exact (pf p)
end 

example: ∀ (b:bool), bor b tt = tt := 
begin
assume b,
cases b with T F,
apply eq.refl tt, 
apply eq.refl tt,
end 

example: ∀ (n: ℕ ), n = 0 ∨ n ≠ 0 := 
begin
assume (n: ℕ) ,
cases n with Z P,
apply or.inl(eq.refl 0),
apply or.inr _,
assume h,
cases h,
end

/-
FINAL:
As long as you are solid on HW 9 you are solid for the final.
-/