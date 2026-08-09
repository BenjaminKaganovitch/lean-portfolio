import Mathlib

/-!
# SparseInt partial order

A partial order on a copy of `ℤ` whose only strict relations are `2k ≤ 2k + 1` for `k ≥ 0`.
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
    intro hab hbc
    rcases hab with rfl | ⟨h1, h2, h3⟩
    · exact hbc
    · rcases hbc with rfl | ⟨h4, h5, h6⟩
      · exact Or.inr ⟨h1, h2, h3⟩
      · exfalso
        omega
  le_antisymm a b := by
    intro hab hba
    rcases hab with rfl | ⟨-, -, h1⟩
    · rfl
    · rcases hba with h' | ⟨-, -, h2⟩
      · exact h'.symm
      · exfalso
        omega

lemma le_def {a b : SparseInt} :
    a ≤ b ↔ a = b ∨ (0 ≤ toInt a ∧ toInt a % 2 = 0 ∧ toInt b = toInt a + 1) :=
  Iff.rfl

end SparseInt

end LeanPortfolio.OrderTheory
