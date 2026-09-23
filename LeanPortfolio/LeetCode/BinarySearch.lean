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
decreasing_by all_goals omega

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

theorem search_complete (a : Array Int) (target : Int) (hs : Sorted a) (lo hi : ℕ)
    (hhi : hi ≤ a.size) (h : search a target lo hi = none) :
    ∀ k, lo ≤ k → k < hi → a[k]! ≠ target := by
  fun_induction search a target lo hi with
  | case1 lo hi hlt heq => simp at h
  | case2 lo hi hlt hne hlt' ih =>
    intro k hk1 hk2 hkt
    by_cases hk : (lo + hi) / 2 + 1 ≤ k
    · exact ih hhi h k hk hk2 hkt
    · -- `k ≤ mid`, so `a[k] ≤ a[mid] < target`
      have := hs k ((lo + hi) / 2) (by omega) (by omega)
      rw [hkt] at this
      exact absurd hlt' (not_lt.mpr this)
  | case3 lo hi hlt hne hge ih =>
    intro k hk1 hk2 hkt
    by_cases hk : k < (lo + hi) / 2
    · exact ih (by omega) h k hk1 hk hkt
    · -- `mid ≤ k`, so `target ≤ a[mid] ≤ a[k] = target`, forcing `a[mid] = target`
      have := hs ((lo + hi) / 2) k (by omega) (by omega)
      rw [hkt] at this
      exact hne (le_antisymm this (not_lt.mp hge))
  | case4 lo hi hge =>
    intro k hk1 hk2
    omega

theorem binarySearch_spec (a : Array Int) (target : Int) (hs : Sorted a) :
    BinarySearchSpec a target (binarySearch a target) := by
  constructor
  · intro i h
    have hsnd := search_sound a target 0 a.size i h
    exact ⟨hsnd.1, hsnd.2⟩
  · intro h i hi
    exact search_complete a target hs 0 a.size le_rfl h i (Nat.zero_le _) hi

lemma needs_sorted : binarySearch #[2, 3, 1] 1 = none := by
  simp [binarySearch, search]

lemma needs_sorted_spec : ¬ BinarySearchSpec #[2, 3, 1] 1 (binarySearch #[2, 3, 1] 1) := by
  intro h
  have := h.2 needs_sorted 2 (by simp)
  simp at this

end LeanPortfolio.LeetCode.BinarySearch
