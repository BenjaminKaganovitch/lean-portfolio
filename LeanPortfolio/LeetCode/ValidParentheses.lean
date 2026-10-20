import Mathlib

/-!
# Valid Parentheses (LeetCode 20)

Decide whether every bracket in a string over `()[]{}` is closed by one of the same type,
in the right order.
-/

namespace LeanPortfolio.LeetCode.ValidParentheses

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

inductive Balanced : List Char → Prop
  | nil : Balanced []
  | wrap {o c : Char} {l : List Char} : IsPair o c → Balanced l → Balanced (o :: (l ++ [c]))
  | append {l₁ l₂ : List Char} : Balanced l₁ → Balanced l₂ → Balanced (l₁ ++ l₂)

def ValidSpec (l : List Char) (r : Bool) : Prop :=
  r = true ↔ Balanced l

/-- `stack` holds the unmatched opening brackets, most recent first. -/
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
      by_cases hB : B = []
      · subst hB
        simp only [List.append_nil] at hl'
        subst hl'
        simpa using Balanced.append (Balanced.wrap hp' hl) (Balanced.pair hp)
      · rcases List.eq_nil_or_concat B with rfl | ⟨B', d, hB'⟩
        · contradiction
        · rw [hB', List.concat_eq_append, ← List.append_assoc] at hl'
          obtain ⟨hl'', hcd⟩ := List.append_inj' hl' rfl
          simp only [List.cons.injEq, and_true] at hcd
          subst hcd
          have hinner := Balanced.wrap hp' (ih A' B' hl'')
          have hwrap : (o' :: A') ++ o :: c :: (B' ++ [c']) =
              o' :: ((A' ++ o :: c :: B') ++ [c']) := by simp
          rw [hB', List.concat_eq_append, hwrap]
          exact hinner
  | @append l₁ l₂ h₁ h₂ ih₁ ih₂ =>
    intro A B hAB
    rcases List.append_eq_append_iff.mp hAB with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · simpa using Balanced.append h₁ (ih₂ a' B rfl)
    · simpa using Balanced.append (ih₁ A c' rfl) h₂

/-- If the scan accepts, the pending openers followed by the rest form a valid string. -/
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

lemma rejects_mismatch : isValidList ['(', ']'] = false := by decide

lemma not_balanced_mismatch : ¬ Balanced ['(', ']'] := by
  intro h
  have := (isValidList_spec _).mpr h
  revert this
  decide

lemma accepts_nested : isValidList ['(', '[', ']', '{', '}', ')'] = true := by decide

end LeanPortfolio.LeetCode.ValidParentheses
