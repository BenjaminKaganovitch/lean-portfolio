import Mathlib

/-!
# A monotone bijection of a finite poset is an order isomorphism

The informal claim: if `α` is a finite partial order and `f : α → α` is a monotone
bijection, then `f a ≤ f b` implies `a ≤ b`, so `f` is an order isomorphism.
`le_of_map_le` is the main theorem, `map_le_map_iff` the resulting iff, and
`orderIsoOfMonotoneBijective` packages `f` as an `α ≃o α`.

## Design notes

* The naive statement drops finiteness and is false. `naive_false` refutes it with
  `SparseInt`: the integers, where the only relations besides `a ≤ a` are `2k ≤ 2k + 1`
  for `k ≥ 0`. The shift `n ↦ n + 2` is a monotone bijection, it sends `-2, -1` to
  `0, 1`, and `0 ≤ 1` holds while `-2 ≤ -1` does not. The shift creates relations
  without destroying any. `le_of_map_le` shows this cannot happen on a finite poset.
* `naive_false` quantifies over `α : Type`. The counterexample lives in `Type`, and one
  counterexample there is enough to refute the naive claim.
* `SparseInt` is a type synonym (`def SparseInt : Type := ℤ`) with explicit `toInt` and
  `ofInt`, so its `PartialOrder` never meets the usual order on `ℤ`. Statements about
  `SparseInt` go through `toInt`, which makes the arithmetic visible to `omega`.
* Proof idea for the fixed theorem: `f` induces a map on the finite set of pairs
  `{(a, b) | a ≤ b}`, sending `(a, b)` to `(f a, f b)`. This map is injective because `f`
  is, so it is surjective. Then `(f a, f b)` with `f a ≤ f b` has a preimage `(a', b')`
  with `a' ≤ b'`, and injectivity of `f` gives `a' = a`, `b' = b`.
* Only injectivity of `f` is used. On a finite type that is equivalent to bijectivity, so
  the statement keeps `Function.Bijective` to match the informal claim.
* Prior formalizations: none found in Mathlib (grep, Loogle, LeanSearch). Other public
  repositories were not searched. No public formalization was consulted.
-/

namespace LeanPortfolio.OrderTheory

/-- The integers with a sparse partial order: `a ≤ b` iff `a = b`, or `a = 2k` with
`k ≥ 0` and `b = a + 1`. -/
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

/-- Shift by two. -/
def shift (n : SparseInt) : SparseInt := ofInt (toInt n + 2)

lemma shift_monotone : Monotone shift := by
  intro a b h
  rw [le_def] at h ⊢
  rcases h with rfl | ⟨h1, h2, h3⟩
  · exact Or.inl rfl
  · right
    simp only [shift, toInt_ofInt]
    omega

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

/-- Without finiteness the statement fails on `SparseInt`. -/
theorem naive_false :
    ¬ ∀ (α : Type) [PartialOrder α] (f : α → α), Monotone f → Function.Bijective f →
      ∀ a b, f a ≤ f b → a ≤ b := by
  intro h
  exact SparseInt.not_le
    (h SparseInt SparseInt.shift SparseInt.shift_monotone SparseInt.shift_bijective _ _
      SparseInt.shift_le)

theorem le_of_map_le {α : Type*} [PartialOrder α] [Finite α] {f : α → α}
    (hf : Monotone f) (hb : Function.Bijective f) {a b : α} (h : f a ≤ f b) : a ≤ b := by
  -- `f` acting on the finite set of related pairs
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

/-- A monotone bijection of a finite poset, as an order isomorphism. -/
noncomputable def orderIsoOfMonotoneBijective {α : Type*} [PartialOrder α] [Finite α]
    {f : α → α} (hf : Monotone f) (hb : Function.Bijective f) : α ≃o α where
  toEquiv := Equiv.ofBijective f hb
  map_rel_iff' := map_le_map_iff hf hb

@[simp] lemma coe_orderIsoOfMonotoneBijective {α : Type*} [PartialOrder α] [Finite α]
    {f : α → α} (hf : Monotone f) (hb : Function.Bijective f) :
    ⇑(orderIsoOfMonotoneBijective hf hb) = f :=
  rfl

end LeanPortfolio.OrderTheory

#print axioms LeanPortfolio.OrderTheory.naive_false
#print axioms LeanPortfolio.OrderTheory.le_of_map_le
#print axioms LeanPortfolio.OrderTheory.map_le_map_iff
#print axioms LeanPortfolio.OrderTheory.orderIsoOfMonotoneBijective
