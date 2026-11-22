/-
Author: Confidence U. Oghosa
Repository: https://github.com/FIddo-tech/MathFormulations
-/

import Mathlib

/-!
# Sum of the First n Natural Numbers

Formula: ∑_{i=0}^{n} i = n * (n + 1) / 2

Formalized in the non-divisive form `2 * (∑_{i=0}^{n} i) = n * (n + 1)` to avoid
truncation in natural-number division.
-/

/-- Recursive definition of the sum 0 + 1 + ... + n -/
def sumFirstN : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumFirstN n

theorem sumFirstN_two_mul (n : ℕ) : 2 * sumFirstN n = n * (n + 1) := by
  induction n with
  | zero => simp [sumFirstN]
  | succ n ih =>
    -- unfold: 2 * ((n + 1) + sumFirstN n) = (n + 1) * (n + 1 + 1)
    simp only [sumFirstN]
    rw [Nat.mul_add, ih]
    ring
