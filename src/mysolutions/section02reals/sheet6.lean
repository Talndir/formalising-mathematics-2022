/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import mysolutions.section02reals.sheet5 -- import a bunch of previous stuff

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in a solutions video,
so if you like you can try some of them and then watch me
solving them.

Good luck! 
-/

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : 0 < c) : tendsto (λ n, c * a n) (c * t) :=
begin
  rw tendsto_def at h ⊢,
  intros ε hε,
  specialize h (ε/c) (div_pos hε hc),
  ring_nf,
  simp_rw [abs_mul, abs_of_pos hc, ← lt_div_iff hc],
  have w : t < ε/c → t * c < ε, { exact (lt_div_iff hc).mp },
  exact h
end

/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsto_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : tendsto a t) :
  tendsto (λ n, 37 * a n) (37 * t) :=
begin
  exact tendsto_pos_const_mul h (by linarith)
end

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : c < 0) : tendsto (λ n, c * a n) (c * t) :=
begin
  have h' : tendsto (λ n, -(-c * a n)) (-(-c * t)) :=
  by exact tendsto_neg (tendsto_pos_const_mul h (by linarith)),
  norm_num at h',
  exact h'
end

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsto_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, c * a n) (c * t) :=
begin
  by_cases hc : c = 0,
  { rw hc,
    ring_nf,
    exact tendsto_const 0 },
  { by_cases hc' : c > 0,
    { exact tendsto_pos_const_mul h hc' },
    { have hc' : c < 0 := (ne.le_iff_lt hc).mp (le_of_not_gt hc'),
      exact tendsto_neg_const_mul h hc' } }
end

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsto_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, a n * c) (t * c) :=
begin
  simp_rw [mul_comm, mul_comm t c],
  exact tendsto_const_mul c h
end

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tendsto_neg' {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  convert tendsto_const_mul (-1) ha, -- read about `convert` on the community web pages
  { ext, simp }, -- ext is a generic extensionality tactic. Here it's being
                 -- used to deduce that two functions are the same if they take
                 -- the same values everywhere
  { simp },
end

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsto_of_tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (h1 : tendsto (λ n, a n - b n) t) (h2 : tendsto b u) :
  tendsto a (t+u) :=
begin
  convert tendsto_add h1 h2,
  ext,
  norm_num,
end

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsto_sub_lim {a : ℕ → ℝ} {t : ℝ}
  (h : tendsto a t) : tendsto (λ n, a n - t) 0 :=
begin
  convert tendsto_sub h (tendsto_const t),
  norm_num,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsto_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : tendsto a t)
  (hb : tendsto b u) : tendsto (λ n, a n * b n) (t * u) :=
begin
  rw tendsto_def at ha hb ⊢,
  intros ε hε,
  let ε' := ε / (2 + |t| + |u|),
  have ε'd : ε' = ε / (2 + |t| + |u|) := rfl,
  have hε'' : 2 + |t| + |u| > 0,
  { rw add_assoc,
    apply add_pos_of_pos_of_nonneg,
    { simp },
    { apply add_nonneg,
      exact abs_nonneg t,
      exact abs_nonneg u } },
  have hε' : ε' > 0 := div_pos hε hε'',
  have hc := hb,
  obtain ⟨Ba, hBa⟩ := ha ε' hε',
  obtain ⟨Bb, hBb⟩ := hb ε' hε',
  obtain ⟨Bc, hBc⟩ := hc 1 (by linarith),
  have hBounded : ∀ x y : ℝ, |x - y| < 1 → |x| < 1 + |y|,
    { intros x y h,
      have h' : |x| - |y| ≤ |x - y| := abs_sub_abs_le_abs_sub x y,
      linarith },
  use (max Ba (max Bb Bc)),
  intros n hn,
  have hFactor : |a n * b n - t * u| = |b n * (a n - t) + t * (b n - u)| := by ring_nf,
  rw hFactor,
  have hSplit : |b n * (a n - t) + t * (b n - u)| ≤ |b n| * |a n - t| + |t| * |b n - u|,
    { have h1 : ∀ {x y z : ℝ}, |x * (y - z)| = |x| * |y - z|,
      { intros x y z, exact abs_mul x (y - z) },
      rw ← h1, rw ← h1,
      exact abs_add (b n * (a n - t)) (t * (b n - u)) },
  have h1 : |b n| * |a n - t| + |t| * |b n - u| ≤ |b n| * ε' + |t| * ε',
    { have ha : |a n - t| < ε' := by { exact hBa n (le_of_max_le_left hn) },
      have hb : |b n - u| < ε' := by { exact hBb n (le_of_max_le_left (le_of_max_le_right hn)) },
      have hh : ∀ {x y z : ℝ}, 0 ≤ x → y < z → x * y ≤ x * z,
        { intros x y z hx hyz,
          by_cases hx' : 0 = x, { rw ← hx', ring_nf }, {
            exact le_of_lt ((mul_lt_mul_left ((ne.le_iff_lt hx').mp hx)).mpr hyz) } },
      have ha' : |b n| * |a n - t| ≤ |b n| * ε' := hh (abs_nonneg (b n)) ha,
      have hb' : |t| * |b n - u| ≤ |t| * ε' := hh (abs_nonneg t) hb,
      linarith },
  apply lt_of_le_of_lt hSplit,
  apply lt_of_le_of_lt h1,
  clear ha hb hc hBa hBb hFactor hSplit h1,
  have hbu : ε' * |b n| + |t| * ε' < ε' * (1 + |u|) + |t| * ε', {
    have h' : |b n| < (1 + |u|) := hBounded (b n) u (hBc n (le_of_max_le_right (le_of_max_le_right hn))),
    exact (add_lt_add_iff_right (|t| * ε')).mpr ((mul_lt_mul_left hε').mpr h') },
  ring_nf at hbu,
  rw ← add_mul (|b n|) (|t|) ε',
  apply lt_trans hbu,
  rw ε'd,
  have hdiv : ∀ x y z : ℝ, x * (y / z) = (x / z) * y, { intros x y z, ring },
  rw hdiv (|t| + (|u| + 1)) ε (2 + |t| + |u|),
  have hdiv' : ∀ x y: ℝ, 0 < y → x < 1 → x * y < y,
  { intros x y hy hxy, apply (mul_lt_iff_lt_one_left hy).mpr, exact hxy },
  apply hdiv' ((|t| + (|u| + 1)) / (2 + |t| + |u|)) ε hε,
  have hdiv'' : ∀ x y: ℝ, 0 < y → x < y → x / y < 1,
  { intros x y hy hxy, exact (div_lt_one hy).mpr hxy },
  apply hdiv'' (|t| + (|u| + 1)) (2 + |t| + |u|) hε'',
  ring_nf,
  linarith
end

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsto_zero_mul_tendsto_zero
  {a b : ℕ → ℝ} (ha : tendsto a 0) (hb : tendsto b 0) :
  tendsto (λ n, a n * b n) 0 :=
begin
  convert tendsto_mul a b 0 0 ha hb,
  norm_num,
end

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsto_unique (a : ℕ → ℝ) (s t : ℝ)
  (hs : tendsto a s) (ht : tendsto a t) : s = t :=
begin
  by_contra,
  have ht : tendsto (λ n, - a n) (-t) := tendsto_neg ht,
  have hst : tendsto (λ n, a n - a n) (s - t) := tendsto_add hs ht,
  simp at hst,
  have h : |s - t| > 0, { cases lt_or_gt_of_ne h; { simp, linarith } },
  obtain ⟨B, hB⟩ := hst (|s - t|) (by linarith),
  specialize hB B (le_refl B),
  dsimp at hB,
  ring_nf at hB,
  have h'' : ∀ x y : ℝ, -x + y = -(x - y), { intros x y, ring },
  have h' : |s - t| < |s - t|, { nth_rewrite 0 ← abs_neg (s - t), rw ← h'' s t, exact hB },
  exact (lt_self_iff_false (|s - t|)).mp h'
end
