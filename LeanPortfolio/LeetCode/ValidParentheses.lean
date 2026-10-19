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

instance (o c : Char) : Decidable (IsPair o c) :=
  if h1 : o = '(' ∧ c = ')' then isTrue (Or.inl h1)
  else if h2 : o = '[' ∧ c = ']' then isTrue (Or.inr (Or.inl h2))
  else if h3 : o = '{' ∧ c = '}' then isTrue (Or.inr (Or.inr h3))
  else isFalse (by
    rintro (h | h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h)

instance (c : Char) : Decidable (IsOpen c) :=
  if h1 : c = '(' then isTrue (Or.inl h1)
  else if h2 : c = '[' then isTrue (Or.inr (Or.inl h2))
  else if h3 : c = '{' then isTrue (Or.inr (Or.inr h3))
  else isFalse (by
    rintro (rfl | rfl | rfl)
    · exact h1 rfl
    · exact h2 rfl
    · exact h3 rfl)

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

def isValid (s : String) : Bool := isValidList s.toList

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

end LeanPortfolio.LeetCode.ValidParentheses
