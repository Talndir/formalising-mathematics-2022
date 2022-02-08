/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ∪ A = A :=
begin
  ext,
  split,
  { rintro (h | h);
    exact h, },
  { intro h,
    left,
    exact h, }
end

example : A ∩ A = A :=
begin
  ext,
  split; intro h,
  { exact h.left, },
  { exact ⟨h,h⟩, }
end

example : A ⊆ B → B ⊆ A → A = B :=
begin
  intros h1 h2,
  ext,
  split; intro h,
  { exact h1 h, },
  { exact h2 h, }
end

example : A ∩ B = B ∩ A :=
begin
  rw [inter_def, inter_def],
  simp_rw and_comm,
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  ext,
  repeat { rw mem_inter_iff },
  rw and_assoc,
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  ext,
  repeat { rw mem_union },
  rw or_assoc,
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  ext,
  rw [mem_inter_iff, mem_union, mem_union, mem_union, mem_inter_iff],
  rw or_and_distrib_left,
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext,
  rw [mem_inter_iff, mem_union, mem_union, mem_inter_iff, mem_inter_iff],
  rw and_or_distrib_left,
end

