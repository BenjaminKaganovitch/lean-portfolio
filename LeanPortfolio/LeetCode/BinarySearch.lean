import Mathlib

/-!
# Binary Search (LeetCode 704)

Given a sorted `a : Array Int` and `target : Int`, return an index `i` with
`a[i] = target`, or `none` if `target` does not occur.

## Design notes

* `BinarySearchSpec` is the full spec. `some i` must be an in-range index holding
  `target`, and `none` must mean `target` occurs nowhere in the array.
* `WeakSpec` keeps only the first half: "if you return an index, it is correct". The
  constant `none` meets it on every input, since it never returns an index.
  `weak_spec_insufficient` proves this and shows the full spec rejects it on `#[1]`,
  target `1`. The missing half is completeness, and it is the half that needs the
  sortedness hypothesis.
* `WeakSpec` really is weaker: `BinarySearchSpec.weak` shows every correct result meets it.
* Sortedness is non-decreasing order, so duplicates are allowed and any matching index
  is accepted. LeetCode promises distinct values, which the proof does not need.
* Soundness (`search_sound`) holds for any array. Completeness (`search_complete`) uses
  `Sorted`, and `needs_sorted` shows it fails without it: on `#[2, 3, 1]` the search
  misses `1`.
* The search keeps a half-open window `[lo, hi)` and probes `(lo + hi) / 2`. Indices are
  natural numbers, so the classic overflow in `lo + hi` cannot happen here. That is a
  difference between this model and fixed-width code, not something the proof covers.
  Termination is by `hi - lo`.
* Prior work: VERINA (`verina_basic_51`) has a related insertion-index task with its
  proof left as `sorry`. Nothing for this problem was found in human-eval-lean or CLEVER.
  Only task descriptions were read. Other public repositories were not searched.
-/

namespace LeanPortfolio.LeetCode.BinarySearch

/-- Non-decreasing order. -/
def Sorted (a : Array Int) : Prop :=
  ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!

/-- Full spec: a returned index holds `target`, and `none` means `target` is absent. -/
def BinarySearchSpec (a : Array Int) (target : Int) (r : Option ℕ) : Prop :=
  (∀ i, r = some i → i < a.size ∧ a[i]! = target) ∧
  (r = none → ∀ i, i < a.size → a[i]! ≠ target)

/-- Weak spec: only soundness of a returned index. -/
def WeakSpec (a : Array Int) (target : Int) (r : Option ℕ) : Prop :=
  ∀ i, r = some i → i < a.size ∧ a[i]! = target

theorem BinarySearchSpec.weak {a : Array Int} {target : Int} {r : Option ℕ}
    (h : BinarySearchSpec a target r) : WeakSpec a target r :=
  h.1

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
  refine ⟨fun i h => ?_, fun h i hi => ?_⟩
  · have := search_sound a target 0 a.size i h
    exact ⟨this.1, this.2⟩
  · exact search_complete a target hs 0 a.size le_rfl h i (Nat.zero_le _) hi

/-- Without sortedness the search can miss an element that is present. -/
lemma needs_sorted : binarySearch #[2, 3, 1] 1 = none := by
  simp [binarySearch, search]

/-- Wrong: never finds anything. -/
def searchWrong (_a : Array Int) (_target : Int) : Option ℕ := none

lemma sorted_singleton (x : Int) : Sorted #[x] := by
  intro i j hij hj
  simp only [List.size_toArray, List.length_singleton] at hj
  obtain rfl : j = 0 := by omega
  obtain rfl : i = 0 := by omega
  exact le_rfl

/-- `WeakSpec` admits an implementation that violates the full spec. -/
theorem weak_spec_insufficient :
    ∃ impl : Array Int → Int → Option ℕ,
      (∀ a target, Sorted a → WeakSpec a target (impl a target)) ∧
      ¬ ∀ a target, Sorted a → BinarySearchSpec a target (impl a target) := by
  refine ⟨searchWrong, fun a target _ i h => by simp [searchWrong] at h, fun h => ?_⟩
  have := (h #[1] 1 (sorted_singleton 1)).2 rfl 0 (by simp)
  simp at this

end LeanPortfolio.LeetCode.BinarySearch

#print axioms LeanPortfolio.LeetCode.BinarySearch.binarySearch_spec
#print axioms LeanPortfolio.LeetCode.BinarySearch.BinarySearchSpec.weak
#print axioms LeanPortfolio.LeetCode.BinarySearch.needs_sorted
#print axioms LeanPortfolio.LeetCode.BinarySearch.weak_spec_insufficient
