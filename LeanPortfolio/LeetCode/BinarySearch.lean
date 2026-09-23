import Mathlib

/-!
# Binary Search (LeetCode 704)

Given a sorted `a : Array Int`, return an index holding `target`, or `none` if it is
absent.
-/

namespace LeanPortfolio.LeetCode.BinarySearch

def Sorted (a : Array Int) : Prop :=
  ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!

def BinarySearchSpec (a : Array Int) (target : Int) (r : Option ℕ) : Prop :=
  (∀ i, r = some i → i < a.size ∧ a[i]! = target) ∧
  (r = none → ∀ i, i < a.size → a[i]! ≠ target)

/-- Search the half-open window `[lo, hi)`. -/
def search (a : Array Int) (target : Int) (lo hi : ℕ) : Option ℕ :=
  if lo < hi then
    if a[(lo + hi) / 2]! = target then some ((lo + hi) / 2)
    else if a[(lo + hi) / 2]! < target then search a target ((lo + hi) / 2 + 1) hi
    else search a target lo ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

def binarySearch (a : Array Int) (target : Int) : Option ℕ :=
  search a target 0 a.size

theorem search_sound (a : Array Int) (target : Int) (lo hi i : ℕ)
    (h : search a target lo hi = some i) : i < hi ∧ a[i]! = target := by
  fun_induction search a target lo hi with
  | case1 lo hi hlt heq =>
    obtain rfl := Option.some.inj h
    exact ⟨by omega, heq⟩
  | case2 lo hi hlt hne hlt' ih => exact ih h
  | case3 lo hi hlt hne hge ih => exact ⟨by have := (ih h).1; omega, (ih h).2⟩
  | case4 lo hi hge => simp at h

end LeanPortfolio.LeetCode.BinarySearch
