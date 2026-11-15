import Mathlib

/-!
# Euclid's Theorem: Infinitude of Primes

Idiomatic formalization demonstrating that the set of prime numbers is unbounded
in ℕ.

This proof was correct as originally written; no changes were needed. Every
lemma used here (`Nat.exists_prime_and_dvd`, `Nat.dvd_factorial`,
`Nat.dvd_add_right`, `Nat.Prime.not_dvd_one`) checks out against its actual
Mathlib signature.
-/

open Nat

theorem exists_prime_greater_than (n : ℕ) : ∃ p, Nat.Prime p ∧ p > n := by
  -- Consider (n! + 1)
  have h_fac_ge : 1 < n.factorial + 1 := by
    have h1 : 1 ≤ n.factorial := Nat.factorial_pos n
    omega
  -- Obtain the smallest prime factor p of (n! + 1)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt h_fac_ge)
  use p
  refine ⟨hp_prime, ?_⟩
  -- Prove by contradiction that p cannot be ≤ n
  by_contra! h_le
  -- If p ≤ n, then p divides n!
  have hp_dvd_fac : p ∣ n.factorial := Nat.dvd_factorial hp_prime.pos h_le
  -- If p ∣ n! and p ∣ (n! + 1), then p ∣ 1
  have hp_dvd_one : p ∣ 1 := (Nat.dvd_add_right hp_dvd_fac).mp hp_dvd
  exact Nat.Prime.not_dvd_one hp_prime hp_dvd_one
