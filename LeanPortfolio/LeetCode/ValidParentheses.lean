import Mathlib

/-!
# Valid Parentheses (LeetCode 20)

Given a string of the characters `()[]{}`, decide whether every bracket is closed by a
bracket of the same type, in the correct order.

## Design notes

* `Balanced` is the grammar of valid strings: the empty string, `o w c` for a matching
  pair `o, c` and a valid `w`, and the concatenation of two valid strings. `IsPair` lists
  the three pairs, so `(]` is not valid: `rejects_mismatch` checks the implementation on
  it and `not_balanced_mismatch` derives that it is not in the grammar. A spec that
  treated all brackets as one type would accept it.
* `ValidSpec l r` says `r = true ↔ Balanced l`. `isValidList` is the usual stack scan,
  and `isValidList_spec` proves both directions. The hard direction uses
  `Balanced.insert`: putting a matching pair anywhere into a valid string keeps it valid.
* `WeakSpec` asks only that accepted strings have matching counts of each bracket type,
  plus that valid strings are accepted. `countCheck` compares the counts and meets it on
  every input. It accepts `)(` and `([)]`, neither of which is valid.
  `weak_spec_insufficient` proves this using `)(`.
* `ValidSpec.weak` shows every correct result also meets `WeakSpec`, using
  `Balanced.countsMatch`.
* LeetCode inputs contain only bracket characters. Any other character is treated as a
  closing bracket that matches nothing, so the scan rejects it, and the grammar has no
  rule that produces it.
* `isValid` on `String` goes through `String.toList`. The proofs are about `List Char`.
* Prior work: human-eval-lean proves a one-type version (`Common/Brackets.lean`, used by
  HumanEval 56 and 61), which cannot tell `(]` from `()`. AlgoVeri (`bracket_matching`)
  and CLEVER state related tasks with proofs left as `sorry`. Only task descriptions,
  declaration names and file statistics were read, no proofs. Other public repositories
  were not searched.
-/

namespace LeanPortfolio.LeetCode.ValidParentheses

/-- The three bracket pairs. -/
def IsPair (o c : Char) : Prop :=
  (o = '(' ∧ c = ')') ∨ (o = '[' ∧ c = ']') ∨ (o = '{' ∧ c = '}')

def IsOpen (c : Char) : Prop :=
  c = '(' ∨ c = '[' ∨ c = '{'

instance (o c : Char) : Decidable (IsPair o c) := by unfold IsPair; infer_instance

instance (c : Char) : Decidable (IsOpen c) := by unfold IsOpen; infer_instance

lemma IsPair.isOpen {o c : Char} (h : IsPair o c) : IsOpen o := by
  unfold IsPair at h; unfold IsOpen
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

lemma IsPair.not_isOpen {o c : Char} (h : IsPair o c) : ¬ IsOpen c := by
  unfold IsPair at h; unfold IsOpen
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

/-- Valid bracket strings. -/
inductive Balanced : List Char → Prop
  | nil : Balanced []
  | wrap {o c : Char} {l : List Char} : IsPair o c → Balanced l → Balanced (o :: (l ++ [c]))
  | append {l₁ l₂ : List Char} : Balanced l₁ → Balanced l₂ → Balanced (l₁ ++ l₂)

/-- Full spec: accept exactly the valid strings. -/
def ValidSpec (l : List Char) (r : Bool) : Prop :=
  r = true ↔ Balanced l

/-- Same number of opening and closing brackets of each type. -/
def CountsMatch (l : List Char) : Prop :=
  l.count '(' = l.count ')' ∧ l.count '[' = l.count ']' ∧ l.count '{' = l.count '}'

/-- Weak spec: accepted strings have matching counts, and valid strings are accepted. -/
def WeakSpec (l : List Char) (r : Bool) : Prop :=
  (r = true → CountsMatch l) ∧ (Balanced l → r = true)

/-- Stack scan. `stack` holds the unmatched opening brackets, most recent first. -/
def scan : List Char → List Char → Bool
  | [], stack => stack.isEmpty
  | c :: cs, stack =>
    if IsOpen c then scan cs (c :: stack)
    else
      match stack with
      | o :: st => if IsPair o c then scan cs st else false
      | [] => false

def isValidList (l : List Char) : Bool := scan l []

lemma scan_open {c : Char} {cs stack : List Char} (hc : IsOpen c) :
    scan (c :: cs) stack = scan cs (c :: stack) := by
  simp [scan, hc]

lemma scan_close {c o : Char} {cs st : List Char} (hc : ¬ IsOpen c) :
    scan (c :: cs) (o :: st) = if IsPair o c then scan cs st else false := by
  simp [scan, hc]

lemma scan_close_nil {c : Char} {cs : List Char} (hc : ¬ IsOpen c) :
    scan (c :: cs) [] = false := by
  simp [scan, hc]

def isValid (s : String) : Bool := isValidList s.toList

lemma Balanced.pair {o c : Char} (h : IsPair o c) : Balanced [o, c] := by
  simpa using Balanced.wrap h Balanced.nil

lemma Balanced.countsMatch {l : List Char} (h : Balanced l) : CountsMatch l := by
  induction h with
  | nil => simp [CountsMatch]
  | wrap hp _ ih =>
    unfold IsPair at hp
    unfold CountsMatch at ih ⊢
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [List.count_append] <;> omega
  | append _ _ ih₁ ih₂ =>
    unfold CountsMatch at ih₁ ih₂ ⊢
    simp only [List.count_append]
    omega

/-- A valid prefix is consumed by the scan without touching the stack. -/
lemma scan_balanced_append {l : List Char} (h : Balanced l) :
    ∀ rest stack, scan (l ++ rest) stack = scan rest stack := by
  induction h with
  | nil => intro rest stack; rfl
  | @wrap o c l hp _ ih =>
    intro rest stack
    have e : o :: (l ++ [c]) ++ rest = o :: (l ++ c :: rest) := by simp
    rw [e, scan_open hp.isOpen, ih, scan_close hp.not_isOpen, if_pos hp]
  | append _ _ ih₁ ih₂ =>
    intro rest stack
    rw [List.append_assoc, ih₁, ih₂]

/-- Inserting a matching pair anywhere into a valid string keeps it valid. -/
lemma Balanced.insert {o c : Char} (hp : IsPair o c) {w : List Char} (h : Balanced w) :
    ∀ A B, w = A ++ B → Balanced (A ++ o :: c :: B) := by
  induction h with
  | nil =>
    intro A B hAB
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hAB.symm
    exact Balanced.pair hp
  | @wrap o' c' l hp' hl ih =>
    intro A B hAB
    cases A with
    | nil =>
      simp only [List.nil_append] at hAB ⊢
      subst hAB
      simpa using Balanced.append (Balanced.pair hp) (Balanced.wrap hp' hl)
    | cons a A' =>
      simp only [List.cons_append, List.cons.injEq] at hAB
      obtain ⟨rfl, hl'⟩ := hAB
      rcases List.eq_nil_or_concat B with rfl | ⟨B', d, rfl⟩
      · simp only [List.append_nil] at hl'
        subst hl'
        simpa using Balanced.append (Balanced.wrap hp' hl) (Balanced.pair hp)
      · rw [List.concat_eq_append, ← List.append_assoc] at hl'
        obtain ⟨hl'', hcd⟩ := List.append_inj' hl' rfl
        simp only [List.cons.injEq, and_true] at hcd
        subst hcd
        have := Balanced.wrap hp' (ih A' B' hl'')
        simpa using this
  | @append l₁ l₂ h₁ h₂ ih₁ ih₂ =>
    intro A B hAB
    rcases List.append_eq_append_iff.mp hAB with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · simpa using Balanced.append h₁ (ih₂ a' B rfl)
    · simpa using Balanced.append (ih₁ A c' rfl) h₂

/-- If the scan accepts, the consumed opening brackets plus the rest form a valid string. -/
lemma balanced_of_scan :
    ∀ (l stack : List Char), scan l stack = true → Balanced (stack.reverse ++ l) := by
  intro l
  induction l with
  | nil =>
    intro stack h
    simp only [scan, List.isEmpty_iff] at h
    subst h
    exact Balanced.nil
  | cons c cs ih =>
    intro stack h
    by_cases hc : IsOpen c
    · rw [scan_open hc] at h
      simpa using ih (c :: stack) h
    · cases stack with
      | nil => simp [scan_close_nil hc] at h
      | cons o st =>
        rw [scan_close hc] at h
        by_cases hp : IsPair o c
        · rw [if_pos hp] at h
          simpa using (ih st h).insert hp st.reverse cs rfl
        · simp [hp] at h

theorem isValidList_spec (l : List Char) : ValidSpec l (isValidList l) := by
  constructor
  · intro h
    simpa using balanced_of_scan l [] h
  · intro h
    have := scan_balanced_append h [] []
    simpa [isValidList, scan] using this

theorem isValid_iff (s : String) : isValid s = true ↔ Balanced s.toList :=
  isValidList_spec s.toList

theorem ValidSpec.weak {l : List Char} {r : Bool} (h : ValidSpec l r) : WeakSpec l r :=
  ⟨fun hr => (h.mp hr).countsMatch, h.mpr⟩

/-- The three types matter: a mismatched pair is rejected. -/
lemma rejects_mismatch : isValidList ['(', ']'] = false := by decide

lemma not_balanced_mismatch : ¬ Balanced ['(', ']'] := by
  intro h
  have := (isValidList_spec _).mpr h
  revert this
  decide

lemma accepts_nested : isValidList ['(', '[', ']', '{', '}', ')'] = true := by decide

/-- Wrong: only compares counts. -/
def countCheck (l : List Char) : Bool :=
  l.count '(' == l.count ')' && l.count '[' == l.count ']' && l.count '{' == l.count '}'

lemma countCheck_iff (l : List Char) : countCheck l = true ↔ CountsMatch l := by
  simp [countCheck, CountsMatch, and_assoc]

theorem countCheck_weak (l : List Char) : WeakSpec l (countCheck l) :=
  ⟨(countCheck_iff l).mp, fun h => (countCheck_iff l).mpr h.countsMatch⟩

lemma countCheck_crossed : countCheck ['(', '[', ')', ']'] = true := by decide

/-- `WeakSpec` admits an implementation that violates the full spec. -/
theorem weak_spec_insufficient :
    ∃ impl : List Char → Bool,
      (∀ l, WeakSpec l (impl l)) ∧ ¬ ∀ l, ValidSpec l (impl l) := by
  refine ⟨countCheck, countCheck_weak, fun h => ?_⟩
  have hb : Balanced [')', '('] := (h [')', '(']).mp (by decide)
  have := (isValidList_spec [')', '(']).mpr hb
  revert this
  decide

end LeanPortfolio.LeetCode.ValidParentheses

#print axioms LeanPortfolio.LeetCode.ValidParentheses.isValidList_spec
#print axioms LeanPortfolio.LeetCode.ValidParentheses.isValid_iff
#print axioms LeanPortfolio.LeetCode.ValidParentheses.ValidSpec.weak
#print axioms LeanPortfolio.LeetCode.ValidParentheses.not_balanced_mismatch
#print axioms LeanPortfolio.LeetCode.ValidParentheses.weak_spec_insufficient
