/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Making ℤ from ℕ²

You can define `ℤ` as ℕ² / ≈, where (a,b) ≈ (c,d) ↔ a + d = b + c.
This sheet goes through this (definition, commutative ring structure) with very few hints.
All the techniques are things we've seen in the earlier sheets.

Hint: if the tactic state is

h : a + d = b + c
⊢ c + b = d + a

you can close the goal with `linarith`. If things get nonlinear (multiplication,
I'm looking at you), there's always `nlinarith`.

-/

/-

# Warm-up: how products work in Lean

-/

-- constructor for ℕ × ℕ 

example : ℕ × ℕ := (3,4)

-- eliminators

def foo : ℕ × ℕ := (37, 53)

example : foo.1 = 37 := 
begin
  refl
end

example : foo.2 = 53 := 
begin
  refl
end

-- warning : constructor on eliminators isn't refl
example (a : ℕ × ℕ) : a = (a.1, a.2) :=
begin
  -- refl fails
  cases a with x y, -- a term of type ℕ × ℕ is a pair; `cases` takes it apart.
  -- now refl works
  refl,
end

def R (ab cd : ℕ × ℕ) : Prop :=
ab.1 + cd.2 = ab.2 + cd.1

lemma R_def (ab cd : ℕ × ℕ) :
R ab cd ↔ ab.1 + cd.2 = ab.2 + cd.1 := 
begin
  refl,
end

lemma R_def' (a b c d : ℕ) :
R (a, b) (c, d) ↔ a + d = b + c :=
begin
  refl,
end 


lemma R_refl : reflexive R :=
begin
  intro x,
  unfold R,
  linarith,
end

lemma R_symm : symmetric R :=
begin
  intros x y h,
  unfold R at h ⊢,
  linarith,
end

lemma R_trans : transitive R :=
begin
  intros x y z h1 h2,
  unfold R at h1 h2 ⊢,
  linarith,
end

instance s : setoid (ℕ × ℕ) :=
{ r := R,
  iseqv := ⟨R_refl, R_symm, R_trans⟩ }

@[simp] lemma equiv_def (a b c d : ℕ) :
  (a, b) ≈ (c, d) ↔ a + d = b + c :=
begin
  refl,
end

notation `myint` := quotient s

-- Amusingly, we can't now make a myint namespace unless
-- we do some weird quote thing (Lean unfolds the notation otherwise)
namespace «myint»

instance : has_zero myint :=
{ zero := ⟦(0,0)⟧ }

@[simp] lemma zero_def : (0 : myint) = ⟦(0, 0)⟧ :=
begin
  refl,
end

def neg : myint → myint :=
quotient.map (λ ab, (ab.2, ab.1)) begin
  intros a b h,
  dsimp,
  rw [equiv_def, eq_comm],
  exact h,
end

instance : has_neg myint :=
{ neg := neg }

@[simp] lemma neg_def (a b : ℕ) : 
  -⟦(a, b)⟧ = ⟦(b, a)⟧ :=
begin
  refl,
end

def add : myint → myint → myint :=
quotient.map₂ (λ ab cd, (ab.1 + cd.1, ab.2 + cd.2)) begin
  intros a b h1 x y h2,
  dsimp,
  rw equiv_def,
  change R a b at h1,
  change R x y at h2,
  rw R_def at h1 h2,
  linarith,
end

instance : has_add myint :=
{ add := add }

@[simp] lemma add_def (a b c d : ℕ) :
  ⟦(a, b)⟧ + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ :=
begin
  refl,
end

instance add_comm_group : add_comm_group myint :=
{ add := (+),
  add_assoc := begin
    intros a b c,
    apply quotient.induction_on₃ a b c, clear a b c,
    intros a b c,
    apply quotient.sound,
    dsimp,
    rw equiv_def,
    ring,
  end,
  zero := 0,
  zero_add := begin
    intros a,
    apply quotient.induction_on a, clear a,
    intros a,
    apply quotient.sound,
    simp,
  end,
  add_zero := begin
    intros a,
    apply quotient.induction_on a, clear a,
    intros a,
    apply quotient.sound,
    simp,
  end,
  neg := has_neg.neg,
  add_left_neg := begin
    intros a,
    apply quotient.induction_on a, clear a,
    intros a,
    apply quotient.sound,
    dsimp,
    rw equiv_def,
    linarith,
  end,
  add_comm := begin
    intros a b,
    apply quotient.induction_on₂ a b, clear a b,
    intros a b,
    apply quotient.sound,
    dsimp,
    rw equiv_def,
    linarith,
  end }

-- our model is that the equivalence class ⟦(a, b)⟧
-- represents the integer a - b
instance : has_one myint :=
{ one := ⟦(1, 0)⟧}

@[simp] lemma one_def : (1 : myint) = ⟦(1, 0)⟧ :=
begin
  refl,
end

-- (a-b)*(c-d)=(ac+bd)-(ad+bc)
def mul : myint → myint → myint :=
quotient.map₂ (λ ab cd, (ab.1 * cd.1 + ab.2 * cd.2, ab.1 * cd.2 + ab.2 * cd.1)) begin
  intros a b h1 x y h2,
  dsimp,
  rw equiv_def,
  change R a b at h1,
  change R x y at h2,
  rw R_def at h1 h2,
  nlinarith,
end

instance : has_mul myint :=
{ mul := mul }

@[simp] lemma mul_def (a b c d : ℕ) :
  ⟦(a, b)⟧ * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ :=
begin
  refl,
end

instance : comm_ring myint :=
{ add := (+),
  zero := 0,
  mul := (*),
  mul_assoc := begin
    intros a b c,
    apply quotient.induction_on₃ a b c, clear a b c,
    intros a b c,
    apply quotient.sound,
    dsimp,
    rw equiv_def,
    ring,
  end,
  one := 1,
  one_mul := begin
    intros a,
    apply quotient.induction_on a, clear a,
    intros a,
    apply quotient.sound,
    simp,
  end,
  mul_one := begin
    intros a,
    apply quotient.induction_on a, clear a,
    intros a,
    apply quotient.sound,
    simp,
  end,
  left_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c, clear a b c,
    intros a b c,
    apply quotient.sound,
    dsimp,
    rw equiv_def,
    ring,
  end,
  right_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c, clear a b c,
    intros a b c,
    apply quotient.sound,
    dsimp,
    rw equiv_def,
    ring,
  end,
  mul_comm := begin
    intros a b,
    apply quotient.induction_on₂ a b, clear a b,
    intros a b,
    apply quotient.sound,
    dsimp,
    rw equiv_def,
    linarith,
  end,
  ..myint.add_comm_group }

end «myint»

