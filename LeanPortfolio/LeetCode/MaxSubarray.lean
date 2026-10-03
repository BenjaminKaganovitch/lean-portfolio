import Mathlib

/-!
# Maximum Subarray (LeetCode 53)

Return the largest sum of a nonempty contiguous subarray of a nonempty `nums : List Int`.
-/

namespace LeanPortfolio.LeetCode.MaxSubarray

def IsMaxOver (P : List Int → Prop) (v : Int) : Prop :=
  (∃ s, P s ∧ s ≠ [] ∧ s.sum = v) ∧ ∀ s, P s → s ≠ [] → s.sum ≤ v

def MaxSubarraySpec (nums : List Int) (r : Int) : Prop :=
  IsMaxOver (· <:+: nums) r

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
    have key : ∀ s, s <:+: [x] → s ≠ [] → s = [x] := by
      intro s hs hne
      rcases List.infix_cons_iff.mp hs with h | h
      · obtain ⟨t, rfl, ht⟩ := eq_cons_of_prefix_cons h hne
        rw [List.prefix_nil] at ht
        rw [ht]
      · rw [List.infix_nil] at h
        exact absurd h hne
    constructor
    · refine ⟨⟨[x], List.prefix_refl _, by simp, by simp [kadane]⟩, fun s hs hne => ?_⟩
      rw [key s hs.isInfix hne]
      simp [kadane]
    · refine ⟨⟨[x], List.infix_refl _, by simp, by simp [kadane]⟩, fun s hs hne => ?_⟩
      rw [key s hs hne]
      simp [kadane]
  | cons y ys ih =>
    obtain ⟨⟨⟨sp, hsp, hspne, hspsum⟩, hpmax⟩, ⟨⟨si, hsi, hsine, hsisum⟩, himax⟩⟩ := ih y
    have hk : kadane x (y :: ys) =
        (max x (x + (kadane y ys).1),
          max (kadane y ys).2 (max x (x + (kadane y ys).1))) := rfl
    rw [hk]
    set c := (kadane y ys).1
    set b := (kadane y ys).2
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

end LeanPortfolio.LeetCode.MaxSubarray
