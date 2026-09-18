import Mathlib

/-!
# If `|f x - f y| ≤ (x - y) ^ 2` for all real `x, y`, then `f` is constant

Includes the vacuous `x - y ^ 2` variant and the proof via midpoint halving and
`Filter.Tendsto`.
-/

namespace LeanPortfolio.Analysis

theorem naive_hyp_unsat : ¬ ∃ f : ℝ → ℝ, ∀ x y, |f x - f y| ≤ x - y ^ 2 := by
  rintro ⟨f, hf⟩
  have h1 : |f 0 - f 1| ≤ (0 : ℝ) - 1 ^ 2 := hf 0 1
  have h2 : (0 : ℝ) ≤ |f 0 - f 1| := abs_nonneg (f 0 - f 1)
  linarith

theorem naive_vacuous :
    ∀ f : ℝ → ℝ, (∀ x y, |f x - f y| ≤ x - y ^ 2) → ∀ x y, f x = f y := by
  intro f hf _x _y
  exfalso
  exact naive_hyp_unsat ⟨f, hf⟩

theorem abs_sub_le_sq_of_sub_le_sq {f : ℝ → ℝ} (h : ∀ x y, f x - f y ≤ (x - y) ^ 2)
    (x y : ℝ) : |f x - f y| ≤ (x - y) ^ 2 := by
  rw [abs_le]
  refine ⟨?_, h x y⟩
  have h' := h y x
  have e : (y - x) ^ 2 = (x - y) ^ 2 := by ring
  linarith

theorem eq_of_abs_sub_le_sq {f : ℝ → ℝ} (h : ∀ x y, |f x - f y| ≤ (x - y) ^ 2) (x y : ℝ) :
    f x = f y := by
  -- halving the interval `k` times
  have hk : ∀ k : ℕ, ∀ x y, |f x - f y| ≤ (x - y) ^ 2 * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => intro x y; simpa using h x y
    | succ k ih =>
      intro x y
      have h1 := ih x ((x + y) / 2)
      have h2 := ih ((x + y) / 2) y
      calc |f x - f y| = |(f x - f ((x + y) / 2)) + (f ((x + y) / 2) - f y)| := by
            congr 1; ring
        _ ≤ |f x - f ((x + y) / 2)| + |f ((x + y) / 2) - f y| := abs_add_le _ _
        _ ≤ (x - (x + y) / 2) ^ 2 * (1 / 2) ^ k + ((x + y) / 2 - y) ^ 2 * (1 / 2) ^ k :=
            add_le_add h1 h2
        _ = (x - y) ^ 2 * (1 / 2) ^ (k + 1) := by ring
  have hlim : Filter.Tendsto (fun k : ℕ => (x - y) ^ 2 * (1 / 2 : ℝ) ^ k) Filter.atTop
      (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul ((x - y) ^ 2)
  have h0 : |f x - f y| ≤ 0 := ge_of_tendsto' hlim (fun k => hk k x y)
  have := abs_nonpos_iff.mp h0
  linarith

end LeanPortfolio.Analysis
