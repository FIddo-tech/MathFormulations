/-
Author: Confidence U. Oghosa
Repository: https://github.com/FIddo-tech/MathFormulations
-/

import Mathlib

/-!
# Euclid's Theorem: the primes are unbounded in ℕ

For every n there is a prime p > n, via a prime factor of n! + 1.
-/

theorem exists_prime_greater_than (n : ℕ) : ∃ p, Nat.Prime p ∧ p > n := by
  -- n! + 1 ≠ 1, so it has a prime factor p
  have h_pos : 0 < n.factorial := Nat.factorial_pos n
  have h_fac_ge : 1 < n.factorial + 1 := by omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt h_fac_ge)
  refine ⟨p, hp_prime, ?_⟩
  -- Suppose p ≤ n; then p ∣ n!, so p ∣ 1, which is impossible
  by_contra! h_le
  have hp_dvd_fac : p ∣ n.factorial := Nat.dvd_factorial hp_prime.pos h_le
  have hp_dvd_one : p ∣ 1 := (Nat.dvd_add_right hp_dvd_fac).mp hp_dvd
  exact Nat.Prime.not_dvd_one hp_prime hp_dvd_one
