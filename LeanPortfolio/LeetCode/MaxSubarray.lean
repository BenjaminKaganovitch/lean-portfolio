import Mathlib

/-!
# Maximum Subarray (LeetCode 53)

Given a nonempty `nums : List Int`, return the largest sum of a nonempty contiguous
subarray.

## Design notes

* A subarray is a nonempty infix: `s <:+: nums` and `s ≠ []`. Using `List.IsInfix`
  keeps "contiguous" in the statement. Writing `s <+ nums` (`List.Sublist`) instead would
  allow gaps and change the problem.
* `MaxSubarraySpec nums r` says `r` is the sum of some nonempty infix and no nonempty
  infix has a larger sum.
* `WeakSpec` keeps only the first half: "`r` is the sum of some subarray". The wrong
  implementation `maxSubArrayWrong` returns the first element, which is the sum of the
  subarray `[x]`, so it meets `WeakSpec` on every nonempty input. On `[1, 2]` it returns
  `1` while the answer is `3`. `weak_spec_insufficient` proves both facts.
* `MaxSubarraySpec.weak` shows every correct result also meets `WeakSpec`.
* The implementation is Kadane's recurrence. `kadane x l` handles the list `x :: l` and
  returns two numbers: the best sum of a nonempty prefix, and the best sum of a nonempty
  infix. The step is `best prefix of x :: l = max x (x + best prefix of l)`, which is the
  usual "best sum ending here" recurrence read from the right. The recursion follows the
  list structure, so it is linear but not tail recursive.
* LeetCode guarantees at least one element. `maxSubArray [] = 0` is a placeholder, and
  the spec theorem assumes `nums ≠ []`.
* Prior work: VERINA (`verina_advanced_45`, `verina_advanced_75`) and AlgoVeri
  (`maximum_subarray_sum`) state this problem with proofs left as `sorry`.
  human-eval-lean proves the minimum version (HumanEval 114), a different problem. Only
  task descriptions and file statistics were read, no proofs. Other public repositories
  were not searched.
-/

namespace LeanPortfolio.LeetCode.MaxSubarray

/-- `v` is the largest sum over nonempty lists satisfying `P`, and is attained. -/
def IsMaxOver (P : List Int → Prop) (v : Int) : Prop :=
  (∃ s, P s ∧ s ≠ [] ∧ s.sum = v) ∧ ∀ s, P s → s ≠ [] → s.sum ≤ v

/-- Full spec: `r` is the largest sum of a nonempty contiguous subarray. -/
def MaxSubarraySpec (nums : List Int) (r : Int) : Prop :=
  IsMaxOver (· <:+: nums) r

/-- Weak spec: `r` is the sum of some nonempty contiguous subarray. -/
def WeakSpec (nums : List Int) (r : Int) : Prop :=
  ∃ s, s <:+: nums ∧ s ≠ [] ∧ s.sum = r

theorem MaxSubarraySpec.weak {nums : List Int} {r : Int} (h : MaxSubarraySpec nums r) :
    WeakSpec nums r :=
  h.1

/-- Kadane on `x :: l`: (best nonempty prefix sum, best nonempty infix sum). -/
def kadane (x : Int) : List Int → Int × Int
  | [] => (x, x)
  | y :: ys =>
    let r := kadane y ys
    (max x (x + r.1), max r.2 (max x (x + r.1)))

def maxSubArray : List Int → Int
  | [] => 0
  | x :: xs => (kadane x xs).2

lemma eq_cons_of_prefix_cons {x : Int} {l s : List Int} (h : s <+: x :: l) (hs : s ≠ []) :
    ∃ t, s = x :: t ∧ t <+: l := by
  rcases List.prefix_cons_iff.mp h with h | h
  · exact absurd h hs
  · exact h

theorem kadane_spec (x : Int) (l : List Int) :
    IsMaxOver (· <+: x :: l) (kadane x l).1 ∧ IsMaxOver (· <:+: x :: l) (kadane x l).2 := by
  induction l generalizing x with
  | nil =>
    -- the only nonempty infix of `[x]` is `[x]`
    have key : ∀ s, s <:+: [x] → s ≠ [] → s = [x] := by
      intro s hs hne
      rcases List.infix_cons_iff.mp hs with h | h
      · obtain ⟨t, rfl, ht⟩ := eq_cons_of_prefix_cons h hne
        rw [List.prefix_nil] at ht
        rw [ht]
      · rw [List.infix_nil] at h
        exact absurd h hne
    refine ⟨⟨⟨[x], List.prefix_refl _, by simp, by simp [kadane]⟩, fun s hs hne => ?_⟩,
      ⟨⟨[x], List.infix_refl _, by simp, by simp [kadane]⟩, fun s hs hne => ?_⟩⟩
    · rw [key s hs.isInfix hne]
      simp [kadane]
    · rw [key s hs hne]
      simp [kadane]
  | cons y ys ih =>
    obtain ⟨⟨⟨sp, hsp, hspne, hspsum⟩, hpmax⟩, ⟨⟨si, hsi, hsine, hsisum⟩, himax⟩⟩ := ih y
    have hk : kadane x (y :: ys) =
        (max x (x + (kadane y ys).1),
          max (kadane y ys).2 (max x (x + (kadane y ys).1))) := rfl
    rw [hk]
    set c := (kadane y ys).1
    set b := (kadane y ys).2
    -- best prefix of `x :: y :: ys`
    have pre : IsMaxOver (· <+: x :: y :: ys) (max x (x + c)) := by
      constructor
      · rcases le_total (x + c) x with h | h
        · exact ⟨[x], List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩, by simp,
            by simp [max_eq_left h]⟩
        · exact ⟨x :: sp, List.cons_prefix_cons.mpr ⟨rfl, hsp⟩, by simp,
            by simp [hspsum, max_eq_right h]⟩
      · intro s hs hne
        obtain ⟨t, rfl, ht⟩ := eq_cons_of_prefix_cons hs hne
        rcases eq_or_ne t [] with rfl | htne
        · simp
        · have := hpmax t ht htne
          simp only [List.sum_cons]
          exact le_max_of_le_right (by linarith)
    refine ⟨pre, ?_, fun s hs hne => ?_⟩
    · -- attained: either the best infix of the tail or the best prefix here
      rcases le_total (max x (x + c)) b with h | h
      · exact ⟨si, List.infix_cons hsi, hsine, by rw [hsisum, max_eq_left h]⟩
      · obtain ⟨s, hs, hne, hsum⟩ := pre.1
        exact ⟨s, hs.isInfix, hne, by rw [hsum, max_eq_right h]⟩
    · -- an infix of `x :: L` is a prefix of `x :: L` or an infix of `L`
      rcases List.infix_cons_iff.mp hs with h | h
      · exact le_max_of_le_right (pre.2 s h hne)
      · exact le_max_of_le_left (himax s h hne)

theorem maxSubArray_spec (nums : List Int) (h : nums ≠ []) :
    MaxSubarraySpec nums (maxSubArray nums) := by
  cases nums with
  | nil => exact absurd rfl h
  | cons x xs => exact (kadane_spec x xs).2

/-- Wrong: returns the first element. -/
def maxSubArrayWrong : List Int → Int
  | [] => 0
  | x :: _ => x

theorem maxSubArrayWrong_weak (nums : List Int) (h : nums ≠ []) :
    WeakSpec nums (maxSubArrayWrong nums) := by
  cases nums with
  | nil => exact absurd rfl h
  | cons x xs =>
    exact ⟨[x], (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩).isInfix, by simp,
      by simp [maxSubArrayWrong]⟩

/-- `WeakSpec` admits an implementation that violates the full spec. -/
theorem weak_spec_insufficient :
    ∃ impl : List Int → Int,
      (∀ nums, nums ≠ [] → WeakSpec nums (impl nums)) ∧
      ¬ ∀ nums, nums ≠ [] → MaxSubarraySpec nums (impl nums) := by
  refine ⟨maxSubArrayWrong, maxSubArrayWrong_weak, fun h => ?_⟩
  have := (h [1, 2] (by simp)).2 [1, 2] (List.infix_refl _) (by simp)
  simp [maxSubArrayWrong] at this

end LeanPortfolio.LeetCode.MaxSubarray

#print axioms LeanPortfolio.LeetCode.MaxSubarray.maxSubArray_spec
#print axioms LeanPortfolio.LeetCode.MaxSubarray.MaxSubarraySpec.weak
#print axioms LeanPortfolio.LeetCode.MaxSubarray.weak_spec_insufficient
