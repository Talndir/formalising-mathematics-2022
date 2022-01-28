/- # Pointwise and uniform convergence of (real-valued) functions. -/

import tactic
import data.real.basic
import section02reals.sheet3
import project1.limits
import project1.continuity

namespace project1

/- Definitions of pointwise and uniform convergence. -/
def converges (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, tendsto (λ n, f n x) (F x)

theorem converges_def {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} :
  converges f F ↔ ∀ x : ℝ, tendsto (λ n, f n x) (F x) :=
by refl

theorem converges_def2 {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} :
  converges f F ↔ ∀ x : ℝ, ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |f n x - F x| < ε :=
by refl

def unif_converges (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → ∀ x : ℝ, |f n x - F x| < ε

def unif_converges_def {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} :
  unif_converges f F ↔ ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → ∀ x : ℝ, |f n x - F x| < ε :=
by refl

/- Uniform convergence implies pointwise convergence. -/
theorem unif_converges_imp_converges {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
  (h : unif_converges f F) : converges f F :=
begin
  -- Just like continuity, strip off the quantifiers
  -- Once we get to the ∀ x we're done
  rw converges_def2,
  rw unif_converges at h,
  intros x ε hε,
  obtain ⟨B, hB⟩ := h ε hε,
  use B,
  intros n hn,
  exact hB n hn x,
end

/- Uniform convergence preserves continuity. -/
theorem unif_converges_preserves_continuous {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {p : ℝ}
  (hf : unif_converges f F) (hc : ∀ n : ℕ, continuous (f n) p) : continuous F p :=
begin
  -- Just use what we have at each stage - the proof writes itself
  rw continuous_def2,
  rw unif_converges at hf,
  intros ε hε,
  -- Use ε/3 as we will be using the triangle inequality twice
  obtain ⟨B, hB⟩ := hf (ε/3) (by linarith),
  obtain ⟨δ, hδ, hc'⟩ := hc B (ε/3) (by linarith),
  specialize hB B (rfl.ge),
  use [δ, hδ],
  rintro x ⟨hx1, hx2⟩,
  have h1 := hB x,               -- |f_B(x) - F(x)| < ε/3
  have h2 := hc' x ⟨hx1, hx2⟩,    -- |f_B(x) - f_B(p)| < ε/3
  have h3 := hB p,               -- |f_B(p) - F(p)| < ε/3
  simp [abs_sub_comm] at h1,
  simp [abs_lt] at h1 h2 h3 ⊢,
  -- Brute force the inequalities
  cases h1, cases h2, cases h3,
  split; linarith
end

/- Uniform convergence preserves uniform continuity. -/
theorem unif_converges_preserves_unif_continuous {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
  (hf : unif_converges f F) (hc : ∀ n : ℕ, unif_continuous (f n)): unif_continuous F :=
begin
  -- Same proof as above
  rw unif_continuous,
  rw unif_converges at hf,
  intros ε hε,
  -- The same proof works again because ε is independent of y (p in the previous)
  obtain ⟨B, hB⟩ := hf (ε/3) (by linarith),
  obtain ⟨δ, hδ, hc'⟩ := hc B (ε/3) (by linarith),
  specialize hB B (rfl.ge),
  use [δ, hδ],
  rintro x y ⟨hx1, hx2⟩,
  -- Here we use y instead of p
  have h1 := hB x,               -- |f_B(x) - F(x)| < ε/3
  have h2 := hc' x y ⟨hx1, hx2⟩,  -- |f_B(x) - f_B(y)| < ε/3
  have h3 := hB y,               -- |f_B(y) - F(y)| < ε/3
  simp [abs_sub_comm] at h1,
  simp [abs_lt] at h1 h2 h3 ⊢,
  cases h1, cases h2, cases h3,
  split; linarith
end

end project1
