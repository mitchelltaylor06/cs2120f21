/- Group of Mitchell Taylor mbt3vgd@virginia.edu, Denny Garcia lfg3z@virginia.edu 
and Decker Bristow jdb3qn@virginia.edu
-/

/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false :=   -- trick question? why?
/-
It is a trick question because something is only false if it cannot be proven. 
-/
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume porp,
  apply or.elim porp,
    --left disjunct is true
    assume p,
    exact p,
    --right disjunct is true
    assume x,
    exact x,
  -- backwards
  assume P,
  apply or.intro_right,
  exact P,  
end

/-
Assuming P to be a property, we apply the if and only if intro rule
to P ∨ P ↔ P. Assuming porp to be P ∨ P and applying the elimination
rule of or to porp, we require two proofs, one of right P and
one of left P. Assume p is P left and x is P right. Exact both to
get P is P. Assuming P is P, we need a proof that P ∨ P. Apply the or intro rule
to the left to get P. Exact P.

-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume porp,
  apply and.elim_left porp,
  assume P,
  apply and.intro P,
  exact P,
end

/-
Assuming P to be a property, we apply the if and only if intro rule
to P ∧ P ↔ P. Assuming porp to be P ∧ P and applying the elimination
rule of and to the left side of porp, we require a proof of P → P ∧ P. 
Assume P is P. Apply the and intro rule and now a proof of P is P
is required. Exact P.

-/
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  assume porp,
  apply or.elim porp,
  apply or.intro_right,
  apply or.intro_left,
  assume propy,
  cases propy,
  apply or.intro_right,
  exact propy,
  apply or.intro_left,
  exact propy,
end

/-
Assuming P and Q to be a properties, we apply the if and only if intro rule
to P ∨ Q ↔ Q ∨ P. Assuming porp to be P ∨ Q and applying the elimination
rule of or to porp, we require a proof of P → Q ∨ P. Apply or intro rule
to P → Q ∨ P to prove P → P. Assume propy is Q ∨ P and do case analysis.
Apply or intro rule right and then or intro rule left to each case and
exact each.

-/
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  assume porp,
  apply and.intro,
  have q : Q := and.elim_right porp,
  exact q,
  have p : P := and.elim_left porp,
  exact p,
  assume propy,
  apply and.intro,
  have p : P := and.elim_right propy,
  exact p,
  have q : Q := and.elim_left propy,
  exact q,
end

/-
Assuming P and Q to be a properties, we apply the if and only if intro rule
to P ∧ Q ↔ Q ∧ P. Assuming porp to be P ∧ Q and applying the and intro rule,
 we require a proof of P and a proof of Q. Apply and elimination rule to the
right side to of porp to proove Q and to the left side to proove Q. Exact both.
Now assume porpy and repeat the process, with the and elimination of right
prooving P and the left prooving Q.

-/
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  assume porp,
  have p : P := and.elim_left porp,
  have qorr : Q ∨ R := and.elim_right porp,
  cases qorr,
  apply or.intro_left,
  apply and.intro,
  exact p,
  exact qorr,
  apply or.intro_right,
  apply and.intro,
  exact p,
  exact qorr,
  assume x,
  cases x,
  have p : P := and.elim_left x,
  have q: Q := and.elim_right x,
  apply and.intro,
  exact p,
  apply or.intro_left,
  exact q,
  have p : P := and.elim_left x,
  have r : R := and.elim_right x,
  apply and.intro,
  exact p,
  apply or.intro_right,
  exact r,
end

/-
Assuming P and Q to be a properties, we apply the if and only if intro rule
to P ∧ Q ↔ Q ∧ P. Assuming porp to be P ∧ Q and applying the and intro rule,
 we require a proof of P and a proof of Q. Apply and elimination rule to the
right side to of porp to proove Q and to the left side to proove Q. Exact both.
Now assume porpy and repeat the process, with the and elimination of right
prooving P and the left prooving Q. Assuming P and Q to be a properties, we apply the if and only if intro rule
to P ∧ Q ↔ Q ∧ P. Assuming porp to be P ∧ Q and applying the and intro rule,
 we require a proof of P and a proof of Q. Apply and elimination rule to the
right side to of porp to proove Q and to the left side to proove Q. Exact both.
Now assume porpy and repeat the process, with the and elimination of right
prooving P and the left prooving Q.
-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  assume porp,
  apply and.intro,
  cases porp,
  apply or.intro_left,
  exact porp,
  have q : Q := and.elim_left porp,
  apply or.intro_right,
  exact q,
  cases porp,
  apply or.intro_left,
  exact porp,
  have r : R := and.elim_right porp,
  apply or.intro_right,
  exact r,
  assume x,
  have pq : P ∨ Q := and.elim_left x,
  have pr : P ∨ R := and.elim_right x,
  cases pq,
  apply or.intro_left,
  exact pq,
  cases pr,
  apply or.intro_left,
  exact pr,
  apply or.intro_right,
  apply and.intro,
  exact pq,
  exact pr,
end

/-
Assuming P and Q to be a properties, we apply the if and only if intro rule
to P ∧ Q ↔ Q ∧ P. Assuming porp to be P ∧ Q and applying the and intro rule,
 we require a proof of P and a proof of Q. Apply and elimination rule to the
right side to of porp to proove Q and to the left side to proove Q. Exact both.
Now assume porpy and repeat the process, with the and elimination of right
prooving P and the left prooving Q. Assuming P and Q to be a properties, we apply the if and only if intro rule
to P ∧ Q ↔ Q ∧ P. Assuming porp to be P ∧ Q and applying the and intro rule,
 we require a proof of P and a proof of Q. Apply and elimination rule to the
right side to of porp to proove Q and to the left side to proove Q. Exact both.
Now assume porpy and repeat the process, with the and elimination of right
prooving P and the left prooving Q.
-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume x,
  apply and.elim_left x,
  assume y,
  apply and.intro,
  exact y,
  apply or.intro_left,
  exact y,
end

/-
Assume P and Q are properties. Apply the if and only if intro rule to
P ∧ (P ∨ Q) ↔ P. Assuming x to be P ∧ (P ∨ Q), apply the and elimination
rule to the left side of x to proove P. Assume y and apply the intro rule
of and to require a proof of P and a proof of P ∨ Q. Apply the or intro
rule to the left side of P ∨ Q to proove P and exact y.
-/
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume p,
  apply or.elim p,
  assume x,
  exact x,
  assume y,
  apply and.elim_left y,
  assume z,
  apply or.intro_left,
  exact z,
end

/-
Assume P and Q are properties. Apply the if and only if intro rule to
P ∨ (P ∨ Q) ↔ P. Assuming p to be P ∨ (P ∧ Q), apply the or elimination
rule to the to require a proof of P and a proof of Q ∨ P. Assume and
exact x. Assume y and apply the and elimination rule to the left of y.
Assume z and apply the or intro rule to the left. Exact z.
-/
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume porp,
  cases porp,
  apply true.intro,
  exact porp,
  assume x,
  apply or.intro_right,
  exact x,
end

/-
Assume P is a proprty. Apply the if and only if intro rule to 
P ∨ true ↔ true. Assume porp and perform case analysis. On the first
case, apply the true intro rule and exact porp. On the second case,
assume x and apply the or intro rule to the right to proove true.
Exact x.
-/
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume p,
  apply iff.intro,
  assume porp,
  cases porp,
  exact porp,
  cases porp,
  assume x,
  apply or.intro_left,
  exact x,
end
 
 /-
 Assume P is a property. Apply the if and only if intro rule to 
 P ∨ false ↔ P. Assume porp and perform case analysis. On the first
 case, exact porp. On the second case, perform case analysis again.
 Assume x and apply the or intro rule to the left to proove p.
 Exact x.
 -/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume p,
  apply iff.intro,
  assume x,
  apply and.elim_left x,
  assume y,
  apply and.intro y,
  apply true.intro,
end

/-
 Assume P is a property. Apply the if and only if intro rule to 
 P ∨ false ↔ P. Assume porp and perform case analysis. On the first
 case, exact porp. On the second case, perform case analysis again.
 Assume x and apply the or intro rule to the left to proove p.
 Exact x.
 -/
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume p,
  apply iff.intro,
  assume x,
  apply and.elim_right x,
  assume y,
  apply and.intro,
  cases y,
  exact y,
end

/-
 Assume P is a property. Apply the if and only if intro rule to 
 P ∨ false ↔ P. Assume porp and perform case analysis. On the first
 case, exact porp. On the second case, perform case analysis again.
 Assume x and apply the or intro rule to the left to proove p.
 Exact x.
 -/

