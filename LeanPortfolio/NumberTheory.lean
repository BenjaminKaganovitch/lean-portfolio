import Mathlib

/-!
# If `1 ≤ n` and `n ∣ 2 ^ n - 1` then `n = 1`

Informal claim: the only positive integer `n` with `n ∣ 2^n - 1` is `1`.

## Design notes

* Without `1 ≤ n` the statement fails at `n = 0`, since `2 ^ 0 - 1 = 0` and `0 ∣ 0`
  (`naive_false`). The hypothesis is what "positive" meant.
* Truncated subtraction is harmless because `1 ≤ 2 ^ n`. The proof moves to `ZMod p`
  with `Nat.cast_sub`.
* Proof: let `p` be the least prime factor of `n`. The order `d` of `2` in `ZMod p`
  divides `n`, and by Fermat it divides `p - 1`. If `d ≥ 2` it is a divisor of `n` below
  `p`, contradicting minimality, so `d = 1` and `2 = 1` in `ZMod p`.
* Prior formalizations: none found in Mathlib (grep and Loogle) or compfiles (commit
  `1745e6c`). Other public repositories were not searched. The proof was written without
  consulting any existing one.
-/

namespace LeanPortfolio.NumberTheory

theorem naive_false : ¬ ∀ n : ℕ, n ∣ 2 ^ n - 1 → n = 1 := by
  intro h
  exact absurd (h 0 (by norm_num)) (by norm_num)

theorem eq_one_of_dvd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) (h : n ∣ 2 ^ n - 1) : n = 1 := by
  by_contra hne
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime hne
  haveI := Fact.mk hp
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpow : (2 : ZMod p) ^ n = 1 := by
    have h0 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hpn.trans h)
    rw [Nat.cast_sub Nat.one_le_two_pow] at h0
    push_cast at h0
    exact sub_eq_zero.mp h0
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    rw [h2, zero_pow (by omega)] at hpow
    exact zero_ne_one hpow
  have hd_n : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have hd_p : orderOf (2 : ZMod p) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2)
  -- a divisor of `n` below `p` must be `1`
  have hd1 : orderOf (2 : ZMod p) = 1 := by
    by_contra hd1
    have hd0 : orderOf (2 : ZMod p) ≠ 0 := by
      intro h0
      rw [h0] at hd_n
      have := Nat.eq_zero_of_zero_dvd hd_n
      omega
    have hle_p := Nat.le_of_dvd (by have := hp.two_le; omega) hd_p
    have hle_d := Nat.minFac_le_of_dvd (by omega) hd_n
    omega
  rw [orderOf_eq_one_iff] at hd1
  have : (1 : ZMod p) = 0 := by linear_combination hd1
  exact one_ne_zero this

end LeanPortfolio.NumberTheory

#print axioms LeanPortfolio.NumberTheory.naive_false
#print axioms LeanPortfolio.NumberTheory.eq_one_of_dvd_two_pow_sub_one
