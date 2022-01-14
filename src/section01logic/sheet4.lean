/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro pq,
  cases pq with p q,
  exact p
end

example : P ∧ Q → Q :=
begin
  intro pq,
  cases pq with p q,
  exact q
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intros pqr pq,
  cases pq with p q,
  apply pqr,
  exact p, exact q
end

example : P → Q → P ∧ Q :=
begin
  intros p q,
  split,
  exact p, exact q
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro pq,
  cases pq with p q,
  split,
  exact q, exact p
end

example : P → P ∧ true :=
begin
  intro p,
  split,
  exact p, triv
end

example : false → P ∧ false :=
begin
  intro f,
  exfalso,
  exact f
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intros pq qr,
  cases pq with p q,
  cases qr with q' r,
  split,
  exact p, exact r
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros pqr p q,
  apply pqr,
  split,
  exact p, exact q
end



