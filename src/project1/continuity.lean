/- # Continuity and uniform continuity of (real-valued) functions. -/

import tactic
import data.real.basic
import project1.limits

namespace project1

/- Definition of uniform continuity. -/
def unif_continuous (f : ℝ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ δ > 0, ∀ x y : ℝ, 0 < |x - y| ∧ |x - y| < δ → |f x - f y| < ε

theorem unif_continuous_def {f : ℝ → ℝ} :
  unif_continuous f ↔ ∀ ε, 0 < ε → ∃ δ > 0, ∀ x y : ℝ, 0 < |x - y| ∧ |x - y| < δ → |f x - f y| < ε :=
by refl

/- Constant functions are uniformly continuous. -/
theorem unif_continuous_const (c : ℝ) :
  unif_continuous (λ x, c) :=
begin
  rw unif_continuous_def,
  intros ε hε,
  use [1, zero_lt_one],
  rintro x y ⟨h1, h2⟩,
  simpa using hε,
end

/- The identity function is uniformly continuous. -/
theorem unif_continuous_id :
  unif_continuous id :=
begin
  rw unif_continuous_def,
  intros ε hε,
  use [ε, hε],
  simp only [and_imp, imp_self, forall_const, id.def, implies_true_iff],
end

/- The sum of uniformly continuous functions is uniformly continuous. -/
theorem unif_continuous_add {f g : ℝ → ℝ}
  (hf : unif_continuous f) (hg : unif_continuous g) : unif_continuous (λ x, f x + g x) :=
begin
  -- Same strategy as usual: ε/2 then triangle inequality
  -- This proof is identical to the one for limits
  rw unif_continuous_def at *,
  intros ε hε,
  obtain ⟨δf, hδf, hf'⟩ := hf (ε/2) (by linarith),
  obtain ⟨δg, hδg, hg'⟩ := hg (ε/2) (by linarith),
  use [min δf δg, lt_min hδf hδg],
  rintro x y ⟨hx1, hx2⟩,
  obtain hf'' := hf' x y ⟨hx1, (lt_min_iff.mp hx2).left⟩,
  obtain hg'' := hg' x y ⟨hx1, (lt_min_iff.mp hx2).right⟩,
  have h : |f x - f y| + |g x - g y| < ε := by linarith,
  have h : |f x - f y + (g x - g y)| < ε := lt_of_le_of_lt (abs_add (f x - f y) (g x - g y)) h,
  ring_nf at h ⊢,
  exact h,
end

/- If f is uniformly continuous, so is cf. -/
theorem unif_continuous_const_mul {f : ℝ → ℝ} (c : ℝ)
  (hf : unif_continuous f) : unif_continuous (λ x, c * f x) :=
begin
  -- Same proof as for limits
  rw unif_continuous_def at *,
  intros ε hε,
  by_cases hc : c = 0,

  /- c = 0 -/
  { rw hc,
    simp only [exists_prop, gt_iff_lt, zero_mul, sub_zero, abs_zero, ne.def],
    use 1,
    split,
    { linarith },
    { rintro _ _ ⟨_,_⟩, exact hε } },
  
  /- c ≠ 0 -/
  { have hc' : 0 < |c| := abs_pos.mpr hc,
    simp_rw [← mul_sub, abs_mul, ← lt_div_iff' hc'],
    have h : 0 < ε/|c| := div_pos hε hc',
    exact hf (ε/|c|) h },
end

/- Defintion of continuity. -/
def continuous (f : ℝ → ℝ) (p : ℝ) : Prop :=
  limit f p (f p)

theorem continuous_def {f : ℝ → ℝ} {p : ℝ} :
  continuous f p ↔ limit f p (f p) :=
by refl

theorem continuous_def2 {f : ℝ → ℝ} {p : ℝ} :
  continuous f p ↔ ∀ ε, 0 < ε → ∃ δ > 0, ∀ x : ℝ, 0 < |x - p| ∧ |x - p| < δ → |f x - f p| < ε :=
by refl

/- The sum of continuous functions is continuous. -/
theorem continuous_add {f g : ℝ → ℝ} {p : ℝ}
  (hf : continuous f p) (hg : continuous g p) : continuous (λ x, f x + g x) p :=
limit_add hf hg

/- The product of continuous functions is continuous. -/
theorem continuous_mul {f g : ℝ → ℝ} {p : ℝ}
  (hf : continuous f p) (hg : continuous g p) : continuous (λ x, f x * g x) p :=
limit_mul hf hg

/- Uniform continuity implies continuity everywhere. -/
theorem unif_continuous_impl_continuous {f : ℝ → ℝ} :
  unif_continuous f → ∀ x : ℝ, continuous f x :=
begin
  intro hf,
  rw unif_continuous_def at hf,
  intro x,
  rw continuous_def2,
  -- Just eliminate quantifiers, once we get to the ∀ x we're done
  intros ε hε,
  obtain ⟨δ, hδ, hf'⟩ := hf ε hε,
  use [δ, hδ],
  specialize hf' x,
  -- Rename bound variables and rearrange to make Lean see them as equal
  rename_var x y,
  simpa [abs_sub_comm] using hf',
end

end project1
