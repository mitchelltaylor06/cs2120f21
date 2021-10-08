-- Group of Denny Garcia lfg3z@virginia.edu
-- Mitchell Taylor mbt3vgd@virginia.edu
-- Decker Bristow jdb3qn@virginia.edu
-- Aleksander Schultz aps4yj@virginia.edu

-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  apply or.intro_right,
  have qornq := classical.em Q,
  cases qornq,
  assume q,
  apply not.intro h,
  apply and.intro,
  exact p,
  exact q,
  exact qornq,
  apply or.inl,
  exact pn,
  assume h,
  have pornp := classical.em P,
  cases pornp,
  have qornq := classical.em Q,
  cases qornq,
  apply not.intro,
  assume p,
  cases h,
  contradiction,
  contradiction,
  apply not.intro,
  assume p,
  cases h,
  contradiction,
  apply not.intro qornq,
  have q : Q := and.elim_right p,
  exact q,
  apply not.intro,
  assume h,
  have p : P := and.elim_left h,
  contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P,
  assume PQ,
  assume PPQ,
  apply and.intro,
  apply not.intro,
  assume p,
  apply not.intro PPQ,
  apply or.intro_left,
  exact p,
  assume PQ, 
  apply not.intro PPQ,
  apply or.intro_right,
  exact PQ,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  assume p,
  apply or.elim p,
  assume x,
  apply or.intro_left,
  exact x,
  assume p,
  have q : Q := and.elim_right p,
  apply or.intro_right,
  exact q,
  assume y,
  apply or.elim y,
  assume h,
  apply or.intro_left,
  exact h,
  assume x,
  have pornp := classical.em P,
  cases pornp,
  apply or.inl,
  exact pornp,
  apply or.inr,
  apply and.intro,
  exact pornp,
  exact x,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  assume p,
  have porq : P ∨ Q := and.elim_left p,
  have porr : P ∨ R := and.elim_right p,
  apply or.elim porq,
  assume x,
  apply or.intro_left,
  exact x,
  assume y,
  apply or.elim porr,
  assume z,
  apply or.elim porr,
  assume x,
  apply or.intro_left,
  exact z,
  assume h,
  apply or.intro_left,
  exact z,
  assume g,
  apply or.intro_right,
  apply and.intro,
  exact y,
  exact g,
  assume p,
  apply or.elim p,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,
  assume p,
  have q : Q := and.elim_left p,
  have r : R := and.elim_right p,
  apply and.intro,
  apply or.intro_right,
  exact q,
  apply or.intro_right,
  exact r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  assume p,
  have porq : P ∨ Q := and.elim_left p,
  have rors : R ∨ S := and.elim_right p,
  apply or.elim porq,
  assume x,
  apply or.elim rors,
  assume y,
  apply or.intro_left,
  apply and.intro,
  exact x,
  exact y,
  assume z,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro,
  exact x,
  exact z,
  assume a,
  apply or.elim rors,
  assume b,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro,
  exact a,
  exact b,
  assume c,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  apply and.intro,
  exact a,
  exact c,
  assume d,
  apply or.elim d,
  assume e,
  have p : P := and.elim_left e,
  have r : R := and.elim_right e,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact r,
  assume f,
  apply or.elim f,
  assume g,
  have p : P := and.elim_left g,
  have s : S := and.elim_right g,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_right,
  exact s,
  assume i,
  apply or.elim i,
  assume j,
  have q : Q := and.elim_left j,
  have r : R := and.elim_right j,
  apply and.intro,
  apply or.intro_right,
  exact q,
  apply or.intro_left,
  exact r,
  assume k,
  have q : Q := and.elim_left k,
  have s : S := and.elim_right k,
  apply and.intro,
  apply or.intro_right,
  exact q,
  apply or.intro_right,
  exact s,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : exists (n : ℕ), n ≠ 0 :=
begin
  apply exists.intro _ _,
  exact 6,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) := 
begin
  assume P Q,
  apply iff.intro,
  assume p,
  have pnp := classical.em Q,
  have qnq := classical.em P,
  cases pnp,
  apply or.intro_right,
  assumption,
  cases qnq,
  apply or.inr,
  have q : Q := p qnq,
  exact q,
  apply or.inl,
  exact qnq,
  assume x,
  assume p,
  cases x,
  contradiction,
  exact x,
end


-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume p,
  assume x,
  apply not.intro,
  assume h,
  apply not.intro x,
  have q : Q := p h,
  exact q,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume p,
  assume h,
  have pnp := classical.em P,
  have qnq := classical.em Q,
  cases pnp,
  exact pnp,
  have notq : ¬Q := p pnp,
  contradiction,
end

