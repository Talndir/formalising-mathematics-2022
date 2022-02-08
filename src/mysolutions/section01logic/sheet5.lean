/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro pq,
  rw pq
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  { intro pq,
    rw pq },
  { intro qp,
    rw qp }
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros pq qr,
  rwa pq
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  { rintro ⟨p, q⟩,
    exact ⟨q, p⟩ },
  { rintro ⟨q, p⟩,
    exact ⟨p, q⟩ }
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  { rintro ⟨⟨p, q⟩, r⟩,
    exact ⟨p, ⟨q, r⟩⟩ },
  { rintro ⟨p, q, r⟩,
    exact ⟨⟨p, q⟩, r⟩ }
end

example : P ↔ (P ∧ true) :=
begin
  split,
  { intro p,
    split,
    exact p, triv  },
  { rintro ⟨p, -⟩,
    exact p }
end

example : false ↔ (P ∧ false) :=
begin
  split,
  { intro f, cases f },
  { rintro ⟨-,f⟩, exact f }
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros pq rs,
  split,
  { rintro ⟨p, r⟩,
    rw [← pq, ← rs],
    exact ⟨p, r⟩ },
  { rintro ⟨q, s⟩,
    rw [pq, rs],
    exact ⟨q, s⟩ }
end

example : ¬ (P ↔ ¬ P) :=
begin
  intro pnp,
  cases pnp with p np,
  by_cases h : P,
  { exact p h h },
  { exact h (np h) }
end
