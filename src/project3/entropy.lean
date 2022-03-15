/-# Topological entropy. #-/

import tactic
import topology.metric_space.basic
import project3.chaos

open metric set

namespace chaos

variables {X : Type} [topological_space X] [metric_space X] (f : X → X)

#check @is_compact X _ 

noncomputable def maxdist (f : X → X) (N : ℕ) (x y : X) : ℝ :=
  Sup {d : ℝ | ∃ n : ℕ, N ≤ n → d = dist ((f^n) x) ((f^n) y)}

def spanning (n : ℕ) (ε : ℝ) (A : set X) : Prop :=
  ∀ x : X, ∃ y ∈ A, maxdist f n x y < ε

end chaos
