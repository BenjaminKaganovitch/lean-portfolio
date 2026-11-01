import Mathlib

/-!
# Two Sum (LeetCode 1)

Return indices `i < j` with `nums[i] + nums[j] = target`, or `none` if no pair works.

## Design notes

* `TwoSumSpec` bounds every index it reads (`i < j < nums.length`), so `!` never hits its
  default.
* Weak-spec trap: `WeakSpec` asks for `i ≤ j` where `TwoSumSpec` asks for `i < j`, so an
  element can pair with itself. `twoSumWrong` does that and meets `WeakSpec` on every
  input. On LeetCode's Example 2, `[3, 2, 4]` with target `6`, it returns `some (0, 0)`
  where the answer is `(1, 2)` (`weak_spec_insufficient`). Every correct result meets
  `WeakSpec` (`TwoSumSpec.weak`).
* Deviations from LeetCode: no uniqueness assumption, so any valid pair is accepted and
  `none` is required when no pair exists. Indices come in increasing order, so
  `some (1, 0)` is rejected where LeetCode accepts `[1, 0]`, which makes the spec
  stricter than LeetCode.
* The implementation is the quadratic search over pairs. The hash map solution is not
  attempted.
* Prior work: VERINA (`verina_advanced_78` to `80`) has a spec and implementation with no
  completed proof. Nothing found in human-eval-lean, CLEVER or AlgoVeri. Only task
  descriptions were read; other public repositories were not searched.
-/

namespace LeanPortfolio.LeetCode.TwoSum

def TwoSumSpec (nums : List Int) (target : Int) (r : Option (ℕ × ℕ)) : Prop :=
  (∀ i j, r = some (i, j) → i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target) ∧
  (r = none → ∀ i j, i < j → j < nums.length → nums[i]! + nums[j]! ≠ target)

def WeakSpec (nums : List Int) (target : Int) (r : Option (ℕ × ℕ)) : Prop :=
  (∀ i j, r = some (i, j) → i ≤ j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target) ∧
  (r = none → ∀ i j, i < j → j < nums.length → nums[i]! + nums[j]! ≠ target)

theorem TwoSumSpec.weak {nums : List Int} {target : Int} {r : Option (ℕ × ℕ)}
    (h : TwoSumSpec nums target r) : WeakSpec nums target r := by
  refine ⟨fun i j hr => ?_, h.2⟩
  obtain ⟨hij, hj, hs⟩ := h.1 i j hr
  exact ⟨by omega, hj, hs⟩

def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun j => (List.range j).map fun i => (i, j)

lemma mem_pairs {n i j : ℕ} : (i, j) ∈ pairs n ↔ i < j ∧ j < n := by
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨hb, ha⟩
  · rintro ⟨hij, hj⟩
    exact ⟨j, hj, i, hij, rfl, rfl⟩

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

def pairsLe (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun j => (List.range (j + 1)).map fun i => (i, j)

lemma mem_pairsLe {n i j : ℕ} : (i, j) ∈ pairsLe n ↔ i ≤ j ∧ j < n := by
  simp only [pairsLe, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨by omega, ha⟩
  · rintro ⟨hij, hj⟩
    exact ⟨j, hj, i, by omega, rfl, rfl⟩

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
