import Mathlib

/-!
# Energy Conservation in the 1D Harmonic Oscillator

We model a point mass on a spring in one dimension:
  x : ℝ → ℝ (position)
  v : ℝ → ℝ (velocity)
  m, k : ℝ (mass and spring constant, positive parameters)

Newton's second law:
  m * v'(t) + k * x(t) = 0

Energy functional:
  E(t) = (1/2) * m * (v(t))^2 + (1/2) * k * (x(t))^2

We prove that under kinematic and dynamic assumptions, dE/dt = 0.
-/

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
  unfold totalEnergy
  -- d/dt (v^2)
  have pv : HasDerivAt (fun s => (v s) ^ 2) (2 * v t * (- (k / m) * x t)) t := by
    first
    | simpa using (Fma t).pow 2
    | simpa using (Fma t).fun_pow 2
    | (have h := (Fma t).mul (Fma t)
       simp only [pow_two]
       convert h using 1
       ring)
  -- d/dt (x^2)
  have px : HasDerivAt (fun s => (x s) ^ 2) (2 * x t * v t) t := by
    first
    | simpa using (vx t).pow 2
    | simpa using (vx t).fun_pow 2
    | (have h := (vx t).mul (vx t)
       simp only [pow_two]
       convert h using 1
       ring)
  -- Kinetic energy derivative
  have dK : HasDerivAt (fun s => (1 / 2) * m * (v s) ^ 2)
      ((1 / 2) * m * (2 * v t * (- (k / m) * x t))) t :=
    pv.const_mul ((1 / 2) * m)
  -- Potential energy derivative
  have dU : HasDerivAt (fun s => (1 / 2) * k * (x s) ^ 2)
      ((1 / 2) * k * (2 * x t * v t)) t :=
    px.const_mul ((1 / 2) * k)
  -- Sum of derivatives by linearity
  have dE := HasDerivAt.add dK dU
  -- The combined derivative value is algebraically zero
  have hzero :
      (1 / 2) * m * (2 * v t * (- (k / m) * x t)) + (1 / 2) * k * (2 * x t * v t) = 0 := by
    field_simp [hm]
    ring
  rw [hzero] at dE
  exact dE
