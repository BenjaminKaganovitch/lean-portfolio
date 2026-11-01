import Mathlib

/-!
# If `|f x - f y| ≤ (x - y) ^ 2` for all real `x, y`, then `f` is constant

## Design notes

* Naive version: `|f x - f y| ≤ x - y ^ 2`, which Lean parses as `x - (y ^ 2)`.
  `naive_vacuous` states it. It compiles and is proven, and it says nothing about `f`:
  at `x = 0`, `y = 1` the hypothesis reads `|f 0 - f 1| ≤ -1`, so no `f` satisfies it
  (`naive_hyp_unsat`), and the proof only refutes the hypothesis.
* The argument needs midpoints and an exponent above 1. It works over `ℚ` or `ℝ`; over
  `ℤ`, `f n = n` satisfies the bound.
* The one-sided bound `f x - f y ≤ (x - y) ^ 2` is equivalent: swap `x` and `y`
  (`abs_sub_le_sq_of_sub_le_sq`).
* Proof: by induction on `k`, `|f x - f y| ≤ (x - y) ^ 2 * (1 / 2) ^ k`. The step splits
  at the midpoint, each half contributing `((x - y) / 2) ^ 2 * (1 / 2) ^ k`. Then let
  `k → ∞`. No derivatives or mean value theorem.
* Prior formalizations: none found in Mathlib (grep, Loogle, LeanSearch). Other public
  repositories were not searched. No public formalization was consulted.
-/

namespace LeanPortfolio.Analysis

theorem naive_hyp_unsat : ¬ ∃ f : ℝ → ℝ, ∀ x y, |f x - f y| ≤ x - y ^ 2 := by
  rintro ⟨f, hf⟩
  linarith [hf 0 1, abs_nonneg (f 0 - f 1)]

theorem naive_vacuous :
    ∀ f : ℝ → ℝ, (∀ x y, |f x - f y| ≤ x - y ^ 2) → ∀ x y, f x = f y := by
  intro f hf
  exact absurd ⟨f, hf⟩ naive_hyp_unsat

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

#print axioms LeanPortfolio.Analysis.naive_hyp_unsat
#print axioms LeanPortfolio.Analysis.naive_vacuous
#print axioms LeanPortfolio.Analysis.abs_sub_le_sq_of_sub_le_sq
#print axioms LeanPortfolio.Analysis.eq_of_abs_sub_le_sq
