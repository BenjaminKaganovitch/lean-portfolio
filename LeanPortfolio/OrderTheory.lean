import Mathlib

/-!
# A monotone bijection of a finite poset is an order isomorphism

Informal claim: if `α` is a finite partial order and `f : α → α` is a monotone
bijection, then `f a ≤ f b` implies `a ≤ b`, so `f` is an order isomorphism. Main
theorem `le_of_map_le`; `map_le_map_iff` gives the iff and `orderIsoOfMonotoneBijective`
the `α ≃o α`.

## Design notes

* Without finiteness the claim is false (`naive_false`). In `SparseInt`, the integers
  whose only relations besides `a ≤ a` are `2k ≤ 2k + 1` for `k ≥ 0`, the shift
  `n ↦ n + 2` is a monotone bijection sending `-2, -1` to `0, 1`. It creates the relation
  `0 ≤ 1` and destroys none, which `le_of_map_le` rules out on a finite poset.
* `naive_false` quantifies over `α : Type`. One counterexample there refutes the naive
  claim.
* `SparseInt` is a type synonym with explicit `toInt` and `ofInt`, so its order never
  meets the one on `ℤ`, and the arithmetic goes through `toInt` where `omega` can see it.
* Proof: `f` acts injectively on the finite set `{(a, b) | a ≤ b}`, hence surjectively.
  So `(f a, f b)` has a preimage `(a', b')` with `a' ≤ b'`, and injectivity of `f` gives
  `a' = a`, `b' = b`.
* Only injectivity is used. On a finite type it is equivalent to bijectivity, and the
  statement keeps `Function.Bijective` to match the informal claim.
* Prior formalizations: none found in Mathlib (grep, Loogle, LeanSearch). Other public
  repositories were not searched. No public formalization was consulted.
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

#print axioms LeanPortfolio.OrderTheory.naive_false
#print axioms LeanPortfolio.OrderTheory.le_of_map_le
#print axioms LeanPortfolio.OrderTheory.map_le_map_iff
#print axioms LeanPortfolio.OrderTheory.orderIsoOfMonotoneBijective
