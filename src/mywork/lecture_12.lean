/-
We
-/

def ev (n : ℕ) : Prop := n%2=0

example : exists (n : ℕ), ev n :=
begin
  apply exists.intro _ _,
  exact 6,
  apply eq.refl,
end

example : exists n, ev n := _

def pythagorean_triple(a b c : nat) : Prop :=
  a * a + b * b = c * c
example: pythagorean_triple 3 4 5:=
begin
  unfold pythagorean_triple,
  apply eq.refl,
end


example : exists (a b c : ℕ), a*a + b*c = c*c := 



example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end