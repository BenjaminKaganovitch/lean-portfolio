import Mathlib

/-!
# Two Sum (LeetCode 1)

Given `nums : List Int` and `target : Int`, return indices `i < j` with
`nums[i] + nums[j] = target`, or `none` if there are none.

## Design notes

* `TwoSumSpec` is the full spec. A result `some (i, j)` must have `i < j < nums.length`
  and the right sum. A result `none` must mean no pair `i < j` works. Under the stated
  bounds `nums[i]!` is the genuine element, so `!` never hits its default.
* `WeakSpec` differs from `TwoSumSpec` in one place: it asks for `i ≤ j` instead of
  `i < j`. That allows `i = j`, so the same element counts twice. `twoSumWrong` searches
  pairs with `i ≤ j`, and `weak_spec_insufficient` shows it meets `WeakSpec` on every
  input while failing `TwoSumSpec` on LeetCode's Example 2, `nums = [3, 2, 4]`,
  `target = 6`, where it returns `some (0, 0)` instead of the pair `(1, 2)`.
* `WeakSpec` really is weaker: `TwoSumSpec.weak` shows every correct result satisfies it.
  So the weak spec accepts all right answers and some wrong ones.
* LeetCode promises exactly one solution. The spec here does not assume that: any valid
  pair is accepted, and `none` is required when no pair exists.
* LeetCode accepts the two indices in either order. `TwoSumSpec` fixes `i < j`, so it
  rejects `some (1, 0)` where LeetCode would accept `[1, 0]`. This is a normalization
  that makes the spec stricter than LeetCode, not weaker.
* The implementation is the quadratic search over pairs. The point of the file is the
  spec, not the hash map version.
* Prior work: VERINA (`verina_advanced_78` to `80`) states Two Sum with its own spec and
  implementation, but no completed proof. Nothing for this problem was found in
  human-eval-lean, CLEVER or AlgoVeri. Only task descriptions were read. Other public
  repositories were not searched.
-/

namespace LeanPortfolio.LeetCode.TwoSum

/-- Full spec: `some (i, j)` is a valid pair with `i < j`, and `none` means no pair. -/
def TwoSumSpec (nums : List Int) (target : Int) (r : Option (ℕ × ℕ)) : Prop :=
  (∀ i j, r = some (i, j) → i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target) ∧
  (r = none → ∀ i j, i < j → j < nums.length → nums[i]! + nums[j]! ≠ target)

/-- Weak spec: `i ≤ j` in place of `i < j`, so `i = j` is allowed. -/
def WeakSpec (nums : List Int) (target : Int) (r : Option (ℕ × ℕ)) : Prop :=
  (∀ i j, r = some (i, j) → i ≤ j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target) ∧
  (r = none → ∀ i j, i < j → j < nums.length → nums[i]! + nums[j]! ≠ target)

theorem TwoSumSpec.weak {nums : List Int} {target : Int} {r : Option (ℕ × ℕ)}
    (h : TwoSumSpec nums target r) : WeakSpec nums target r := by
  refine ⟨fun i j hr => ?_, h.2⟩
  obtain ⟨hij, hj, hs⟩ := h.1 i j hr
  exact ⟨by omega, hj, hs⟩

/-- All index pairs `(i, j)` with `i < j < n`. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun j => (List.range j).map fun i => (i, j)

lemma mem_pairs {n i j : ℕ} : (i, j) ∈ pairs n ↔ i < j ∧ j < n := by
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨hb, ha⟩
  · rintro ⟨hij, hj⟩
    exact ⟨j, hj, i, hij, rfl, rfl⟩

/-- Quadratic search over pairs `i < j`. -/
def twoSum (nums : List Int) (target : Int) : Option (ℕ × ℕ) :=
  (pairs nums.length).find? fun p => nums[p.1]! + nums[p.2]! == target

theorem twoSum_spec (nums : List Int) (target : Int) :
    TwoSumSpec nums target (twoSum nums target) := by
  constructor
  · intro i j h
    have hmem := mem_pairs.mp (List.mem_of_find?_eq_some h)
    have hp := List.find?_some h
    simp only [beq_iff_eq] at hp
    exact ⟨hmem.1, hmem.2, hp⟩
  · intro h i j hij hj hs
    have := List.find?_eq_none.mp h (i, j) (mem_pairs.mpr ⟨hij, hj⟩)
    simp only [beq_iff_eq] at this
    exact this hs

/-- All index pairs `(i, j)` with `i ≤ j < n`, so including `i = j`. -/
def pairsLe (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun j => (List.range (j + 1)).map fun i => (i, j)

lemma mem_pairsLe {n i j : ℕ} : (i, j) ∈ pairsLe n ↔ i ≤ j ∧ j < n := by
  simp only [pairsLe, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨by omega, ha⟩
  · rintro ⟨hij, hj⟩
    exact ⟨j, hj, i, by omega, rfl, rfl⟩

/-- Wrong: may pair an element with itself. -/
def twoSumWrong (nums : List Int) (target : Int) : Option (ℕ × ℕ) :=
  (pairsLe nums.length).find? fun p => nums[p.1]! + nums[p.2]! == target

theorem twoSumWrong_weak (nums : List Int) (target : Int) :
    WeakSpec nums target (twoSumWrong nums target) := by
  constructor
  · intro i j h
    have hmem := mem_pairsLe.mp (List.mem_of_find?_eq_some h)
    have hp := List.find?_some h
    simp only [beq_iff_eq] at hp
    exact ⟨hmem.1, hmem.2, hp⟩
  · intro h i j hij hj hs
    have := List.find?_eq_none.mp h (i, j) (mem_pairsLe.mpr ⟨by omega, hj⟩)
    simp only [beq_iff_eq] at this
    exact this hs

lemma twoSumWrong_example : twoSumWrong [3, 2, 4] 6 = some (0, 0) := by decide

/-- `WeakSpec` admits an implementation that violates the full spec. -/
theorem weak_spec_insufficient :
    ∃ impl : List Int → Int → Option (ℕ × ℕ),
      (∀ nums target, WeakSpec nums target (impl nums target)) ∧
      ¬ ∀ nums target, TwoSumSpec nums target (impl nums target) := by
  refine ⟨twoSumWrong, twoSumWrong_weak, fun h => ?_⟩
  have := (h [3, 2, 4] 6).1 0 0 twoSumWrong_example
  omega

end LeanPortfolio.LeetCode.TwoSum

#print axioms LeanPortfolio.LeetCode.TwoSum.twoSum_spec
#print axioms LeanPortfolio.LeetCode.TwoSum.TwoSumSpec.weak
#print axioms LeanPortfolio.LeetCode.TwoSum.weak_spec_insufficient
