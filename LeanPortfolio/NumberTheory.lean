import Mathlib

/-!
# If `1 ≤ n` and `n ∣ 2 ^ n - 1` then `n = 1`

Proof via the multiplicative order of `2` modulo the least prime factor `p` of `n`.
-/

namespace LeanPortfolio.NumberTheory

theorem naive_false : ¬ ∀ n : ℕ, n ∣ 2 ^ n - 1 → n = 1 := by
  intro h
  have hdiv : 0 ∣ 2 ^ 0 - 1 := by
    norm_num
  have hzero : (0 : ℕ) = 1 := h 0 hdiv
  exact Nat.zero_ne_one hzero

theorem eq_one_of_dvd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) (h : n ∣ 2 ^ n - 1) : n = 1 := by
  by_contra hne
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpow : (2 : ZMod p) ^ n = 1 := by
    have hdvd : p ∣ 2 ^ n - 1 := hpn.trans h
    have h0 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (2 ^ n - 1) p).mpr hdvd
    have hle : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.cast_sub hle] at h0
    push_cast at h0
    exact sub_eq_zero.mp h0
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpn0 : n ≠ 0 := by omega
    rw [hzero, zero_pow hpn0] at hpow
    exact zero_ne_one hpow
  have hd_n : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have hfermat : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  have hd_p : orderOf (2 : ZMod p) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hfermat
  have hd1 : orderOf (2 : ZMod p) = 1 := by
    by_contra hd1
    have hd0 : orderOf (2 : ZMod p) ≠ 0 := by
      intro h0
      rw [h0] at hd_n
      have hn0 : n = 0 := Nat.eq_zero_of_zero_dvd hd_n
      omega
    have hp2 : 2 ≤ p := hp.two_le
    have hle_p : orderOf (2 : ZMod p) ≤ p - 1 := Nat.le_of_dvd (by omega) hd_p
    have hd2 : 2 ≤ orderOf (2 : ZMod p) := by omega
    have hle_d : p ≤ orderOf (2 : ZMod p) := Nat.minFac_le_of_dvd hd2 hd_n
    omega
  rw [orderOf_eq_one_iff] at hd1
  have hone : (1 : ZMod p) = 0 := by
    linear_combination hd1
  exact one_ne_zero hone

end LeanPortfolio.NumberTheory
