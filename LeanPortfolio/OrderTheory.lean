import Mathlib

/-!
# Infinite poset counterexample to order reflection

The shift `n ↦ n + 2` on `SparseInt` is a monotone bijection that fails to reflect `≤`.
-/

namespace LeanPortfolio.OrderTheory

def SparseInt : Type := ℤ

namespace SparseInt

def toInt : SparseInt → ℤ := id

def ofInt : ℤ → SparseInt := id

@[simp] lemma toInt_ofInt (n : ℤ) : toInt (ofInt n) = n := rfl

lemma toInt_injective : Function.Injective toInt := fun _ _ h => h

instance : PartialOrder SparseInt where
  le a b := a = b ∨ (0 ≤ toInt a ∧ toInt a % 2 = 0 ∧ toInt b = toInt a + 1)
  le_refl _ := Or.inl rfl
  le_trans a b c := by
    rintro (rfl | ⟨h1, h2, h3⟩) (rfl | ⟨h4, h5, h6⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h4, h5, h6⟩
    · exact Or.inr ⟨h1, h2, h3⟩
    · exfalso; omega
  le_antisymm a b := by
    rintro (h | ⟨-, -, h1⟩) (h' | ⟨-, -, h2⟩)
    · exact h
    · exact h
    · exact h'.symm
    · exfalso; omega

lemma le_def {a b : SparseInt} :
    a ≤ b ↔ a = b ∨ (0 ≤ toInt a ∧ toInt a % 2 = 0 ∧ toInt b = toInt a + 1) :=
  Iff.rfl

def shift (n : SparseInt) : SparseInt := ofInt (toInt n + 2)

lemma shift_monotone : Monotone shift := by
  intro a b h
  rw [le_def] at h ⊢
  rcases h with rfl | ⟨h1, h2, h3⟩
  · exact Or.inl rfl
  · right
    simp only [shift, toInt_ofInt]
    refine ⟨by omega, by omega, by omega⟩

lemma shift_bijective : Function.Bijective shift := by
  constructor
  · intro a b h
    apply toInt_injective
    have ht := congrArg toInt h
    simp only [shift, toInt_ofInt] at ht
    omega
  · intro b
    refine ⟨ofInt (toInt b - 2), ?_⟩
    apply toInt_injective
    simp only [shift, toInt_ofInt]
    omega

lemma shift_le : shift (ofInt (-2)) ≤ shift (ofInt (-1)) := by
  rw [le_def]
  right
  simp [shift]

lemma not_le : ¬ ofInt (-2) ≤ ofInt (-1) := by
  rw [le_def]
  rintro (h | ⟨h1, -, -⟩)
  · have := congrArg toInt h
    simp at this
  · simp at h1

end SparseInt

theorem naive_false :
    ¬ ∀ (α : Type) [PartialOrder α] (f : α → α), Monotone f → Function.Bijective f →
      ∀ a b, f a ≤ f b → a ≤ b := by
  intro h
  exact SparseInt.not_le
    (h SparseInt SparseInt.shift SparseInt.shift_monotone SparseInt.shift_bijective _ _
      SparseInt.shift_le)

end LeanPortfolio.OrderTheory
