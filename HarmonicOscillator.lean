/-
Author: Confidence U. Oghosa
Repository: https://github.com/FIddo-tech/MathFormulations
-/

import Mathlib

/-!
# Energy Conservation in the 1D Harmonic Oscillator

Position x : ℝ → ℝ, velocity v : ℝ → ℝ, mass m and spring constant k.
Newton's second law m * v'(t) + k * x(t) = 0 is encoded as v' = -(k / m) * x
(with m ≠ 0). Energy: E(t) = (1/2) m v(t)² + (1/2) k x(t)².

We prove E'(t) = 0 at every t.
-/

/-- Derivative of the square of a differentiable function.
Proved from the product rule, so it does not depend on the argument order of
`HasDerivAt.pow`, which has changed between Mathlib versions. -/
lemma hasDerivAt_sq_aux {f : ℝ → ℝ} {f' t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => f s ^ 2) (2 * f t * f') t := by
  have h2 : HasDerivAt (fun s => f s * f s) (f' * f t + f t * f') t := by
    first | exact h.mul h | exact h.fun_mul h
  convert h2 using 1 <;> first | (funext s; ring) | ring

variable (m k : ℝ)
variable (x v : ℝ → ℝ)

/-- Total mechanical energy of the harmonic oscillator -/
noncomputable def totalEnergy (t : ℝ) : ℝ :=
  (1 / 2) * m * (v t) ^ 2 + (1 / 2) * k * (x t) ^ 2

theorem energy_conserved (t : ℝ)
    (vx : ∀ t, HasDerivAt x (v t) t)
    (Fma : ∀ t, HasDerivAt v (- (k / m) * x t) t)
    (hm : m ≠ 0) :
    HasDerivAt (totalEnergy m k x v) 0 t := by
  show HasDerivAt (fun s => (1 / 2) * m * (v s) ^ 2 + (1 / 2) * k * (x s) ^ 2) 0 t
  -- kinetic part
  have dK : HasDerivAt (fun s => (1 / 2) * m * (v s) ^ 2)
      ((1 / 2) * m * (2 * v t * (- (k / m) * x t))) t := by
    apply HasDerivAt.const_mul
    exact hasDerivAt_sq_aux (Fma t)
  -- potential part
  have dU : HasDerivAt (fun s => (1 / 2) * k * (x s) ^ 2)
      ((1 / 2) * k * (2 * x t * v t)) t := by
    apply HasDerivAt.const_mul
    exact hasDerivAt_sq_aux (vx t)
  have dE := HasDerivAt.add dK dU
  -- the two contributions cancel because m * m⁻¹ = 1 (using m ≠ 0)
  have hzero :
      (1 / 2) * m * (2 * v t * (- (k / m) * x t)) + (1 / 2) * k * (2 * x t * v t) = 0 := by
    first
      | (have hinv : m * m⁻¹ = 1 := mul_inv_cancel₀ hm; linear_combination (-(k * v t * x t)) * hinv)
      | (field_simp [hm]; ring)
      | field_simp [hm]
  rw [hzero] at dE
  exact dE
