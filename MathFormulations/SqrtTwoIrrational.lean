import Mathlib

/-!
# Irrationality of √2 in ℕ

Proof that there exist no coprime natural numbers m and n such that m² = 2 * n²
(with n > 0).

Two bugs were fixed from the original draft:

1. `Nat.even_pow' (h : n ≠ 0) : Even (m ^ n) ↔ Even m` concludes `Even m`
   directly, not a conjunction — so the proof must use `exact h`, not `exact h.1`.

2. `Even m` unfolds to `∃ r, m = r + r`, NOT `∃ r, m = 2 * r`. Destructuring it
   with `rcases ... with ⟨k, rfl⟩` therefore substitutes `m := k + k`, and every
   later step that assumes the `2 * k` form (the `(2 * k) ^ 2` rewrite, and the
   final `Nat.gcd (2 * k) (2 * j)` term) fails to match. The fix is to convert
   to the `2 * k` form explicitly right after destructuring, via `omega` +
   `subst`, instead of relying on `rfl` to hand it to you for free.
-/

lemma even_of_sq_even {m : ℕ} (h : Even (m ^ 2)) : Even m := by
  rw [Nat.even_pow'] at h
  · exact h
  · decide

theorem sqrt2_not_coprime_sq (m n : ℕ) (h_coprime : Nat.Coprime m n) (hn : 0 < n) :
    m ^ 2 ≠ 2 * n ^ 2 := by
  intro h_eq
  -- Step 1: Deduce that m² is even, hence m is even
  have hm2_even : Even (m ^ 2) := by
    use n ^ 2
    linarith
  have hm_even : Even m := even_of_sq_even hm2_even
  obtain ⟨k, hk⟩ := hm_even
  have hm_eq : m = 2 * k := by omega
  subst hm_eq
  -- Step 2: Relate k² to n²
  -- (2 * k)^2 = 4 * k^2 = 2 * n^2 implies 2 * k^2 = n^2
  have hn2_eq : n ^ 2 = 2 * k ^ 2 := by
    have h_expand : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    rw [h_expand] at h_eq
    omega
  -- Step 3: Conclude n² is even, so n is even
  have hn2_even : Even (n ^ 2) := by
    use k ^ 2
    linarith
  have hn_even : Even n := even_of_sq_even hn2_even
  obtain ⟨j, hj⟩ := hn_even
  have hn_eq : n = 2 * j := by omega
  subst hn_eq
  -- Step 4: Contradiction via coprime constraint
  -- Both m and n share 2 as a common divisor
  have h_two_dvd_m : 2 ∣ (2 * k) := dvd_mul_right 2 k
  have h_two_dvd_n : 2 ∣ (2 * j) := dvd_mul_right 2 j
  have h_gcd_ge : 2 ∣ Nat.gcd (2 * k) (2 * j) :=
    Nat.dvd_gcd h_two_dvd_m h_two_dvd_n
  have h_gcd_one : Nat.gcd (2 * k) (2 * j) = 1 := h_coprime
  rw [h_gcd_one] at h_gcd_ge
  -- 2 ∣ 1 is impossible
  revert h_gcd_ge
  decide
