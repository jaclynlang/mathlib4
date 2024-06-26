import Mathlib
open Nat

/-- Any natural number `n ≠ 0` is the product of an odd part `m` and a power of two `2 ^ k`,
   with `k`, `m` natural numbers. -/
theorem Nat.exists_eq_two_pow_mul_odd {n : ℕ} (hn : n ≠ 0) : ∃ k m : ℕ, Odd m ∧ n = 2 ^ k * m :=
  let ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (Nat.succ_ne_self 1)
  ⟨k, m, Nat.odd_iff_not_even.mpr (mt Even.two_dvd hm), hn⟩

/-- `x ^ n + 1` is divisible by `x + 1` only if `n` is odd.  -/
theorem Odd.nat_add_one_dvd_pow_add_one (x : ℕ) {n : ℕ} (hn : Odd n) : x + 1 ∣ x ^ n + 1 := by
  simpa only [one_pow] using hn.nat_add_dvd_pow_add_pow x 1

/-- For `a > 1`, `a ^ b = a` iff `b = 1`. -/
theorem Nat.pow_eq_self_iff (a b : ℕ) (ha : 1 < a) : b = 1 ↔ a ^ b = a := by
  constructor
  · intro h
    rw [h]
    exact Nat.pow_one a
  . intro h
    nth_rewrite 2 [Eq.symm (Nat.pow_one a)] at h
    rw [pow_right_inj (zero_lt_of_lt ha) (Ne.symm (ne_of_lt ha))] at h
    exact h

/-- `a ^ n + 1` is prime only if `n` is a power of two. -/
theorem pow_of_pow_add_prime (a n : ℕ) (ha : 1 < a) (hn : 1 < n) (hP : Nat.Prime (a ^ n + 1)) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (one_pos.trans hn).ne'
  rw [pow_mul] at hP
  use k
  apply (mul_eq_left₀ (Ne.symm (NeZero.ne' (2 ^ k)))).mpr
  by_contra hm'
  have key := hm.nat_add_one_dvd_pow_add_one (a ^ 2 ^ k)
  have not_prime : ¬ ((a ^ 2 ^ k) ^ m + 1).Prime := by
    apply (Nat.not_prime_iff_exists_dvd_ne _).mpr
    . use a ^ 2 ^ k + 1
      have h₁ : a ^ 2 ^ k + 1 ≠ 1 := by
        rw [ne_eq, add_left_eq_self, pow_eq_zero_iff]
        . exact not_eq_zero_of_lt ha
        exact Ne.symm (NeZero.ne' (2 ^ k))
      have h₂ : a ^ 2 ^ k + 1 ≠ (a ^ 2 ^ k) ^ m + 1 := by
        apply Ne.symm
        rw [ne_eq, add_left_inj]
        rw [← Nat.pow_eq_self_iff (a := a ^ 2 ^ k) (b := m)]
        · exact hm'
        · simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
            not_false_eq_true, Nat.one_lt_pow_iff, ha]
      exact ⟨key, h₁, h₂⟩
    . simp only [reduceLeDiff]
      apply one_le_pow
      apply pos_pow_of_pos
      exact zero_lt_of_lt ha
  contradiction
