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

We prove E'(t) = 0 at every t. The closing algebra is discharged with
`field_simp` + `ring` rather than by matching the output shape of `ring_nf`.
-/

variable (m k : ℝ)
variable (x v : ℝ → ℝ)

/-- Total mechanical energy of the harmonic oscillator -/
def totalEnergy (t : ℝ) : ℝ :=
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
    have h_pow := HasDerivAt.pow 2 (Fma t)
    simpa using h_pow
  -- potential part
  have dU : HasDerivAt (fun s => (1 / 2) * k * (x s) ^ 2)
      ((1 / 2) * k * (2 * x t * v t)) t := by
    apply HasDerivAt.const_mul
    have h_pow := HasDerivAt.pow 2 (vx t)
    simpa using h_pow
  have dE := HasDerivAt.add dK dU
  -- the two contributions cancel once k / m is cleared using m ≠ 0
  have hzero :
      (1 / 2) * m * (2 * v t * (- (k / m) * x t)) + (1 / 2) * k * (2 * x t * v t) = 0 := by
    field_simp [hm]
    ring
  rw [hzero] at dE
  exact dE
