/-# Topological definition of chaos. #-/

import tactic
import topology.metric_space.basic

open metric set

namespace chaos

variables {X : Type} [metric_space X] (f : X → X)

notation f `^` n := nat.iterate f n

/- A periodic point is one that eventually returns to its starting point. -/
def is_periodic (x : X) : Prop :=
  ∃ N : ℕ, (f^N) x = x

/- The set of all periodic points. -/
def periodics : set X :=
  {x : X | is_periodic f x}

/- `f` is topologically transitive if for all `U`, `V` open and non-empty, `fⁿ(U)` eventually intersects `V`. -/
def top_trans : Prop :=
  ∀ (U : set X), is_open U ∧ nonempty U → ∀ (V : set X), is_open V ∧ nonempty V → ∃ n : ℕ, (f^n) '' U ∩ V ≠ ∅

/- `f` has sensitive dependence to initial conditions with sensitivity constant `Δ > 0` if for all `x ∈ X` and `ε > 0`, there is some point `y` within `ε` of `x` that eventually moves away further than `Δ` from `x`.
   In other words, all points eventually drift apart under iteration.  -/
def sensitive_dep : Prop :=
  ∃ Δ > 0, ∀ x : X, ∀ ε > 0, ∃ y ∈ ball x ε, ∃ N : ℕ, Δ < dist ((f^N) x) ((f^N) y)

/- `f` is chaotic if it satisfies all of the following:
    - It has dense periodic points.
    - It is topologically transitive.
    - It has sensitive dependence on initial conditions. -/
def chaotic : Prop :=
  dense (periodics f) ∧ top_trans f ∧ sensitive_dep f

/- The orbit of a point is the set of points it visits under iteration. -/
def orbit (x : X) : set X :=
  {y : X | ∃ n : ℕ, (f^n) x = y}


/- If `f` is topologically transitive and `X` is not the orbit of a single point then `f` has sensitive dependence. -/
theorem top_trans_impl_sens_dep (h : ¬∃ x : X, @univ X = orbit f x) (ht : top_trans f) :
  sensitive_dep f :=
begin
  sorry
end

/- `f` is topologically mixing if for all non-empty open sets `U` and `V`, for large enough `N`, `fⁿ(U)` intersects `V` for all `n ≥ N`. -/
def top_mixing : Prop :=
  ∀ (U : set X), is_open U ∧ nonempty U → ∀ (V : set X), is_open V ∧ nonempty V → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f^n) '' U ∩ V ≠ ∅

/- Topological mixing implies topological transitivity. -/
theorem top_mixing_impl_top_trans (ht : top_mixing f) : top_trans f :=
begin
  rintros U ⟨hU,heU⟩ V ⟨hV,heV⟩,
  obtain ⟨N, h⟩ := ht U ⟨hU,heU⟩ V ⟨hV,heV⟩,
  use N,
  exact h N (by linarith),
end

lemma set_mem {X : Type} {Y : set X} (a : X) (h : @univ X = Y) : a ∈ Y :=
begin
  rw ← h,
  exact set.mem_univ a,
end

/- Topological mixing implies sensitive dependence on spaces with more than one point. -/
theorem top_mixing_impl_sens_dep (h : ∃ x y : X, x ≠ y) (ht : top_mixing f) :
  sensitive_dep f :=
begin
  rcases h with ⟨x,y,hxy⟩,
  have hc : ¬∃ x : X, @univ X = orbit f x,
  begin
    by_contra hc,
    rcases hc with ⟨a,ha⟩,
    have x' : x ∈ orbit f a := set_mem x ha,
    have y' : y ∈ orbit f a := set_mem y ha,
    sorry
  end,
  exact top_trans_impl_sens_dep f hc (top_mixing_impl_top_trans f ht),
end

end chaos
