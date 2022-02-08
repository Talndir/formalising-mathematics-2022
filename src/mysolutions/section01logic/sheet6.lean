/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro p,
  left,
  exact p
end

example : Q → P ∨ Q :=
begin
  intro q,
  right,
  exact q
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros pq pr qr,
  cases pq with p q,
  { exact pr p },
  { exact qr q }
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro pq,
  cases pq with p q,
  { right, exact p },
  { left, exact q }
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  { rintro ((p | q) | r),
    left, exact p,
    right, left, exact q,
    right, right, exact r},
  { rintro (p | q | r),
    left, left, exact p,
    left, right, exact q,
    right, exact r}
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros pr qs pq,
  cases pq with p q,
  { left, exact pr p },
  { right, exact qs q }
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros pq pr,
  cases pr with p r,
  { left, exact pq p },
  { right, exact r }
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros pr qs,
  rw [pr, qs]
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  { intro npq,
    split,
    { intro p,
      apply npq,
      left, exact p },
    { intro q,
      apply npq,
      right, exact q } },
  { intro npnq,
    intro pq,
    cases npnq with np nq,
    cases pq with p q,
    { exact np p },
    { exact nq q } }
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  { intro npq,
    by_cases h : P,
    { have g : P → ¬ Q,
      { intros p q,
        exact npq ⟨p, q⟩},
      right,
      exact g h },
    { left, exact h } },
  { rintros npnq ⟨p, q⟩,
    cases npnq with np nq,
    { exact np p },
    { exact nq q} }
end
