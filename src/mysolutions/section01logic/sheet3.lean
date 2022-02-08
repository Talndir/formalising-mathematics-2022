/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro nt,
  apply nt,
  triv
end

example : false → ¬ true :=
begin
  triv
end

example : ¬ false → true :=
begin
  intro nf,
  triv
end

example : true → ¬ false :=
begin
  intro t,
  triv
end

example : false → ¬ P :=
begin
  triv
end

example : P → ¬ P → false :=
begin
  intro p,
  triv
end

example : P → ¬ (¬ P) :=
begin
  intro p,
  triv
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros pq nq p,
  exact nq (pq p)
end

example : ¬ ¬ false → false :=
begin
  intro nnf,
  apply nnf,
  triv
end

-- Not constructive - uses contradiction
example : ¬ ¬ P → P :=
begin
  intro nnp,
  by_contra np,
  exact nnp np
end

-- Also not constructive (although its reverse is constructive)
example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros nqnp p,
  by_contra nq,
  exact nqnp nq p
end