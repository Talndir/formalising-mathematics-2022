/- # Limits of (real-valued) functions and some properties about them. -/

import tactic
import data.real.basic
import data.real.sqrt

namespace project1

/-- Definition of the (two-sided) limit of a function. -/
def limit (f : ℝ → ℝ) (p : ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - p| ∧ |x - p| < δ → |f x - L| < ε

theorem limit_def {f : ℝ → ℝ} {p L : ℝ} :
  limit f p L ↔ ∀ ε, 0 < ε → ∃ δ > 0, ∀ x : ℝ, 0 < |x - p| ∧ |x - p| < δ → |f x - L| < ε :=
by refl

/-- Constant functions tend to the constant everywhere. -/
theorem limit_const (L : ℝ) :
  ∀ p : ℝ, limit (λ x, L) p L :=
begin
  intros p,
  rw limit_def,
  -- Simplify - in particular, the final stage of the goal becomes 0 < ε
  simp only [exists_prop, gt_iff_lt, abs_zero, sub_self],
  intros ε hε,
  use 1,
  split,
  -- 0 < 1
  { linarith },
  -- 0 < ε
  { intros _ _, exact hε },
end

/-- If f → L and g → M at (f + g) → (L + M).
   I.e. Limit of sum is sum of limits. -/
theorem limit_add {f g : ℝ → ℝ} {p L M : ℝ}
  (hf : limit f p L) (hg : limit g p M) : limit (λ x, f x + g x) p (L + M) :=
begin
  rw limit_def at *,
  intros ε hε,
  -- Use ε/2 then add together with triangle inequality later
  obtain ⟨δf, hδf, hf'⟩ := hf (ε/2) (by linarith),
  obtain ⟨δg, hδg, hg'⟩ := hg (ε/2) (by linarith),
  -- Set ε = min δf δg
  use [min δf δg, lt_min hδf hδg],
  rintro x ⟨hx1, hx2⟩,
  obtain hf'' := hf' x ⟨hx1, (lt_min_iff.mp hx2).left⟩,
  obtain hg'' := hg' x ⟨hx1, (lt_min_iff.mp hx2).right⟩,
  -- Triangle inequality and rearranging
  have h : |f x - L| + |g x - M| < ε := by linarith,
  have h : |f x - L + (g x - M)| < ε := lt_of_le_of_lt (abs_add (f x - L) (g x - M)) h,
  ring_nf at h ⊢,
  exact h,
end

/-- If f -> L then cF -> cL. -/
theorem limit_const_mul {f : ℝ → ℝ} {p L : ℝ}
  (hf : limit f p L) (c : ℝ) : limit (λ x, c * f x) p (c * L) :=
begin
  rw limit_def at *,
  intros ε hε,
  by_cases hc : c = 0,

  /- c = 0 -/
  { rw hc,
    simp only [exists_prop, gt_iff_lt, zero_mul, sub_zero, abs_zero, ne.def],
    use 1,
    split,
    -- 0 < 1
    { linarith },
    -- 0 < ε
    { intros _ _, exact hε } },
  
  /- c ≠ 0 -/
  { have hc' : 0 < |c| := abs_pos.mpr hc,
    -- Move the c to the other side
    simp_rw [← mul_sub, abs_mul, ← lt_div_iff' hc'],
    have h : 0 < ε/|c| := div_pos hε hc',
    -- ε/|c| works exactly
    exact hf (ε/|c|) h },
end

/-- If f -> L then f² -> L². -/
theorem limit_square {f : ℝ → ℝ} {p L : ℝ}
  (h : limit f p L) : limit (λ x, f x * f x) p (L * L) :=
begin
  rw limit_def at *,
  intros ε hε,
  -- Use 1/2 (-|L| + sqrt(L² + ε))
  set ε' := 1/2 * (-|L| + real.sqrt (L * L + ε)) with dε',
  have hε' : 0 < ε',
  { have w : |L| < real.sqrt (L * L + ε),
    { -- |L| = sqrt(L²)
      rw ← real.sqrt_mul_self (abs_nonneg L),
      rw abs_mul_abs_self L,
      -- sqrt is monotonic
      apply real.sqrt_lt_sqrt (mul_self_nonneg L),
      -- L² < L² + ε
      linarith },
    simpa },
  
  obtain ⟨δ, hδ, h'⟩ := h ε' hε',
  use [δ, hδ],
  rintro x ⟨hx1, hx2⟩,
  specialize h' x ⟨hx1, hx2⟩,

  -- Bound the main term by a function of ε'
  have he : |f x * f x - L * L| ≤ ε' * ε' + 2 * ε' * |L|,
  { rw (show f x * f x - L * L = (f x + L) * (f x - L), by ring),
    rw abs_mul,
    rw (show f x + L = f x - L + 2 * L, by ring),
    rw (show ε' * ε' + 2 * ε' * |L| = (ε' + 2 * |L|) * ε', by ring),
    -- At this point we have |f x - L + 2 * L| * |f x - L| ≤ (ε' + 2 * |L|) * ε
    apply mul_le_mul,
    -- |f x - L + 2 * L| ≤ ε' + 2 * |L|
    { apply le_trans (abs_add (f x - L) (2 * L)),
      rw abs_mul,
      simpa using le_of_lt h', },
    -- |f x - l| ≤ ε
    { exact le_of_lt h', },
    -- 0 ≤ |f x - L|
    { exact abs_nonneg (f x - L), },
    -- 0 ≤ ε' + 2 * |L|
    { apply add_nonneg,
      exact le_of_lt hε',
      apply mul_nonneg,
      exact zero_le_two,
      exact abs_nonneg L, }, },

  -- Easier to prove by setting e = 2 * ε' and showing
  -- both ε' < e and e * e + 2 * e * |L| = ε
  -- Proving using ε' directly is a nightmare
  set e := -|L| + real.sqrt (L * L + ε) with de,
  have h2 : ε' < e := by linarith,
  have h3 : e * e + 2 * e * |L| = ε,
  { rw de,
    ring_nf,
    rw [pow_two, pow_two, real.mul_self_sqrt, ← abs_mul L L],
    { rw abs_mul_self L,
      ring, },
    { apply add_nonneg,
      exact mul_self_nonneg L,
      exact le_of_lt hε, } },

  -- The final inequality
  have he' : ε' * ε' + 2 * ε' * |L| < ε,
  { have pfe : ε' * ε' < e * e := mul_lt_mul'' h2 h2 (le_of_lt hε') (le_of_lt hε'),
    have pfe' : 2 * ε' * |L| ≤ 2 * e * |L|,
    { apply mul_le_mul,
      linarith,
      linarith,
      exact abs_nonneg L,
      linarith, },
    rw ← h3,
    exact add_lt_add_of_lt_of_le pfe pfe', },
  exact lt_of_le_of_lt he he',
end

/-- If f -> L and g -> M then fg -> LM. -/
theorem limit_mul {f g : ℝ → ℝ} {p L M : ℝ}
  (hf : limit f p L) (hg : limit g p M) : limit (λ x, f x * g x) p (L * M) :=
begin
  -- Recognise that fg = 1/2 * ((f + g)² - f² - g²)
  have h : ∀ x, f x * g x = 1/2 * ((f x + g x) * (f x + g x) + (-1) * (f x * f x) + (-1) * (g x * g x)),
  { intro x, ring, },
  -- Rewrite the limits in the same way
  have h' : L * M = 1 / 2 * ((L + M) * (L + M) + (-1) * (L * L) + (-1) * (M * M)), by ring,
  simp_rw [h, h'],
  -- We can obtain the goal exactly with a combination of const_mul, add and square
  exact limit_const_mul
  ( limit_add
    ( limit_add
      ( limit_square
        ( limit_add hf hg ) )
      ( limit_const_mul
        ( limit_square hf )
        ( -1 ) ) )
    ( limit_const_mul 
      ( limit_square hg )
      ( -1 ) )
  ) (1/2)
end

/-- If f -> L and n : ℕ then fⁿ -> Lⁿ. -/
theorem limit_nonneg_pow {f : ℝ → ℝ} {p L : ℝ}
  (h : limit f p L) (n : ℕ) : limit (λ x, (f x) ^ n) p (L ^ n) :=
begin
  induction n with n ih,
  { simp,
    exact limit_const 1 p, },
  { rw pow_succ,
    simp_rw pow_succ,
    exact limit_mul h ih, }
end

/- Definition of one-sided limits. -/
def limit_left (f : ℝ → ℝ) (p : ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x < p ∧ p - x < δ → |f x - L| < ε

theorem limit_left_def {f : ℝ → ℝ} {p L : ℝ} :
  limit_left f p L ↔ ∀ ε, 0 < ε → ∃ δ > 0, ∀ x : ℝ, x < p ∧ p - x < δ → |f x - L| < ε :=
by refl

def limit_right (f : ℝ → ℝ) (p : ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, p < x ∧ x - p < δ → |f x - L| < ε

theorem limit_right_def {f : ℝ → ℝ} {p L : ℝ} :
  limit_right f p L ↔ ∀ ε, 0 < ε → ∃ δ > 0, ∀ x : ℝ, p < x ∧ x - p < δ → |f x - L| < ε :=
by refl

/-- The two-sided limit exists iff the left and right limits agree. -/
theorem limit_agree_iff {f : ℝ → ℝ} {p L : ℝ} :
  limit f p L ↔ limit_left f p L ∧ limit_right f p L :=
begin
  rw [limit_def, limit_left_def, limit_right_def],
  split,
  /- Two-sided implies one-sided -/
  { intro hf,
    split;
    intros ε hε;
    obtain ⟨δ, hδ, hf'⟩ := hf ε hε;
    use [δ, hδ];
    rintro x ⟨hx1, hx2⟩;
    specialize hf' x,
    
    /- Left limit -/
    { rw abs_sub_comm at hf',
      have h1 : 0 < |p - x| := abs_pos_of_pos (sub_pos.mpr hx1),
      have h2 : |p - x| < δ := by rwa [abs_of_pos (sub_pos.mpr hx1)],
      exact hf' ⟨h1, h2⟩ },

    /- Right limit -/
    { have h1 : 0 < |x - p| := abs_pos_of_pos (sub_pos.mpr hx1),
      have h2 : |x - p| < δ := by rwa [abs_of_pos (sub_pos.mpr hx1)],
      exact hf' ⟨h1, h2⟩  },
  },

  /- One-sided implies two-sided. -/
  { rintro ⟨hf1, hf2⟩,
    intros ε hε,
    obtain ⟨δ1, hδ1, hf1'⟩ := hf1 ε hε,
    obtain ⟨δ2, hδ2, hf2'⟩ := hf2 ε hε,
    -- Use δ = min δ1 δ2
    use [min δ1 δ2, lt_min_iff.mpr ⟨hδ1, hδ2⟩],
    rintro x ⟨hx1, hx2⟩,
    cases (abs_lt.mp hx2) with hx3 hx4,
    
    -- 0 < |x - p| so we have two cases:
    cases lt_or_lt_iff_ne.mpr (abs_pos.mp hx1) with h,

    /- x - p < 0 -/
    { have hx : p - x < min δ1 δ2 := by linarith,
      exact hf1' x ⟨sub_neg.mp h, (lt_min_iff.mp hx).left⟩ },

    /- 0 < x - p -/
    { exact hf2' x ⟨sub_pos.mp h, (lt_min_iff.mp hx4).right⟩ }
  }
end

end project1
