import Mathlib

/-!
# Sum of the First n Natural Numbers

Formula: ∑_{i=0}^{n} i = n * (n + 1) / 2

Implemented via the non-divisive form: 2 * (∑_{i=0}^{n} i) = n * (n + 1)
to avoid natural number truncation during integer division.

This proof was correct as originally written; no changes were needed.
-/

/-- Recursive definition of arithmetic sum from 0 to n -/
def sumFirstN : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumFirstN n

theorem sumFirstN_two_mul (n : ℕ) : 2 * sumFirstN n = n * (n + 1) := by
  induction' n with n ih
  · -- Base case: n = 0
    rfl
  · -- Inductive step: n + 1
    dsimp [sumFirstN]
    -- 2 * ((n + 1) + sumFirstN n) needs the multiplication distributed
    -- before the induction hypothesis can be substituted in.
    rw [Nat.mul_add]
    rw [ih]
    ring
