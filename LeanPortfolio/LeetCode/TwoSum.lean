import Mathlib

/-!
# Two Sum (LeetCode 1)

Return indices `i < j` with `nums[i] + nums[j] = target`, or `none` if no pair works.
-/

namespace LeanPortfolio.LeetCode.TwoSum

def TwoSumSpec (nums : List Int) (target : Int) (r : Option (ℕ × ℕ)) : Prop :=
  (∀ i j, r = some (i, j) → i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target) ∧
  (r = none → ∀ i j, i < j → j < nums.length → nums[i]! + nums[j]! ≠ target)

def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun j => (List.range j).map fun i => (i, j)

lemma mem_pairs {n i j : ℕ} : (i, j) ∈ pairs n ↔ i < j ∧ j < n := by
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · intro h
    rcases h with ⟨a, ha, b, hb, hab⟩
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hb, ha⟩
  · intro h
    rcases h with ⟨hij, hj⟩
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

end LeanPortfolio.LeetCode.TwoSum
