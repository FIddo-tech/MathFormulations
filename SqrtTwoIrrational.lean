/-
Author: Confidence U. Oghosa
Repository: https://github.com/FIddo-tech/MathFormulations
-/

import Mathlib

/-!
# Irrationality of √2, in the coprime form over ℕ

There are no coprime natural numbers m, n (n > 0) with m² = 2 * n².

Pitfall fixed here: `Even m` unfolds to `∃ r, m = r + r`, not `m = 2 * r`.
Destructuring with `rcases ... with ⟨k, rfl⟩` would substitute `m := k + k`,
so later steps written for `2 * k` fail to match syntactically. We therefore
convert explicitly (`omega`) and `subst` the `2 * k` form.
-/

lemma even_of_sq_even {m : ℕ} (h : Even (m ^ 2)) : Even m :=
  (Nat.even_pow' (by norm_num : (2 : ℕ) ≠ 0)).mp h

theorem sqrt2_not_coprime_sq (m n : ℕ) (h_coprime : Nat.Coprime m n) (hn : 0 < n) :
    m ^ 2 ≠ 2 * n ^ 2 := by
  intro h_eq
  -- Step 1: m² is even, hence m is even
  have hm2_even : Even (m ^ 2) := by
    use n ^ 2
    linarith
  obtain ⟨k, hk⟩ := even_of_sq_even hm2_even
  have hm_eq : m = 2 * k := by omega
  subst hm_eq
  -- Step 2: (2k)² = 2n² gives n² = 2k²
  have hn2_eq : n ^ 2 = 2 * k ^ 2 := by
    have h_expand : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    rw [h_expand] at h_eq
    omega
  -- Step 3: n² is even, hence n is even
  have hn2_even : Even (n ^ 2) := by
    use k ^ 2
    linarith
  obtain ⟨j, hj⟩ := even_of_sq_even hn2_even
  have hn_eq : n = 2 * j := by omega
  subst hn_eq
  -- Step 4: 2 divides gcd(2k, 2j) = 1, a contradiction
  have h_gcd_ge : 2 ∣ Nat.gcd (2 * k) (2 * j) :=
    Nat.dvd_gcd (dvd_mul_right 2 k) (dvd_mul_right 2 j)
  have h_gcd_one : Nat.gcd (2 * k) (2 * j) = 1 := h_coprime
  rw [h_gcd_one] at h_gcd_ge
  revert h_gcd_ge
  decide
