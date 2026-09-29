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

end LeanPortfolio.LeetCode.MaxSubarray
