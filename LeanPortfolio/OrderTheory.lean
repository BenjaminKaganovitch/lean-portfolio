import Mathlib

/-!
# A monotone bijection from a finite poset to itself is an order isomorphism

Informal claim: if `α` is a finite partial order and `f : α → α` is a monotone
bijection, then `f a ≤ f b` implies `a ≤ b`, giving an order isomorphism `α ≃o α`.
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
  refine ⟨fun a b h => toInt_injective ?_, fun b => ⟨ofInt (toInt b - 2), toInt_injective ?_⟩⟩
  · have := congrArg toInt h
    simp only [shift, toInt_ofInt] at this
    omega
  · simp [shift]

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

theorem le_of_map_le {α : Type*} [PartialOrder α] [Finite α] {f : α → α}
    (hf : Monotone f) (hb : Function.Bijective f) {a b : α} (h : f a ≤ f b) : a ≤ b := by
  let g : {p : α × α // p.1 ≤ p.2} → {p : α × α // p.1 ≤ p.2} :=
    fun p => ⟨(f p.1.1, f p.1.2), hf p.2⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨x₁, x₂⟩, hx⟩ ⟨⟨y₁, y₂⟩, hy⟩ hxy
    simp only [g, Subtype.mk.injEq, Prod.mk.injEq] at hxy
    obtain rfl := hb.1 hxy.1
    obtain rfl := hb.1 hxy.2
    rfl
  obtain ⟨⟨⟨x, y⟩, hxy⟩, hp⟩ := Finite.injective_iff_surjective.mp hg ⟨(f a, f b), h⟩
  simp only [g, Subtype.mk.injEq, Prod.mk.injEq] at hp
  rw [← hb.1 hp.1, ← hb.1 hp.2]
  exact hxy

theorem map_le_map_iff {α : Type*} [PartialOrder α] [Finite α] {f : α → α}
    (hf : Monotone f) (hb : Function.Bijective f) {a b : α} : f a ≤ f b ↔ a ≤ b :=
  ⟨le_of_map_le hf hb, fun h => hf h⟩

noncomputable def orderIsoOfMonotoneBijective {α : Type*} [PartialOrder α] [Finite α]
    {f : α → α} (hf : Monotone f) (hb : Function.Bijective f) : α ≃o α where
  toEquiv := Equiv.ofBijective f hb
  map_rel_iff' := map_le_map_iff hf hb

@[simp] lemma coe_orderIsoOfMonotoneBijective {α : Type*} [PartialOrder α] [Finite α]
    {f : α → α} (hf : Monotone f) (hb : Function.Bijective f) :
    ⇑(orderIsoOfMonotoneBijective hf hb) = f :=
  rfl

end LeanPortfolio.OrderTheory
