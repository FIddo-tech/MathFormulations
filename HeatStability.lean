/-
Author: Confidence U. Oghosa
Repository: https://github.com/FIddo-tech/MathFormulations
-/

import Mathlib

/-!
# Stability of the explicit (FTCS) scheme for the 1D heat equation

Scheme: u_j^{n+1} = u_j^n + r (u_{j+1}^n - 2 u_j^n + u_{j-1}^n),  r = α Δt / Δx².

* `stepLine_abs_le`           : for 0 ≤ r ≤ 1/2 one step does not increase the max norm.
* `stepDirichlet_abs_le`, `iterate_stepDirichlet_abs_le` : the same with zero boundary values, for all steps.
* `error_accumulation`        : stability turns a per-step defect ε into a global error ≤ M₀ + n ε.
* `stepLine_cos_mode`         : von Neumann amplification factor 1 + 2 r (cos θ - 1).
* `stepLine_unbounded`        : for r > 1/2 the zig-zag mode (-1)^j grows without bound.

Planned (not yet proved): the sine-mode instability on the Dirichlet interval, and a
truncation-error bound O(Δt + Δx²) so that stability and consistency give convergence.
-/

namespace HeatStability

/-- One explicit step on the integer line. -/
def stepLine (r : ℝ) (u : ℤ → ℝ) (j : ℤ) : ℝ :=
  u j + r * (u (j + 1) - 2 * u j + u (j - 1))

/-- One explicit step on the grid with zero boundary values at `j ≤ 0` and `j ≥ N`. -/
def stepDirichlet (r : ℝ) (N : ℤ) (u : ℤ → ℝ) (j : ℤ) : ℝ :=
  if j ≤ 0 ∨ N ≤ j then 0 else stepLine r u j

/-- Discrete maximum principle: for 0 ≤ r ≤ 1/2 the new value is a convex combination. -/
theorem stepLine_abs_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) {u : ℤ → ℝ} {M : ℝ}
    (hu : ∀ j, |u j| ≤ M) (j : ℤ) : |stepLine r u j| ≤ M := by
  have ha := abs_le.1 (hu (j + 1))
  have hb := abs_le.1 (hu j)
  have hc := abs_le.1 (hu (j - 1))
  have hw : 0 ≤ 1 - 2 * r := by linarith
  have a1 : 0 ≤ u (j + 1) + M := by linarith [ha.1]
  have a2 : 0 ≤ M - u (j + 1) := by linarith [ha.2]
  have b1 : 0 ≤ u j + M := by linarith [hb.1]
  have b2 : 0 ≤ M - u j := by linarith [hb.2]
  have c1 : 0 ≤ u (j - 1) + M := by linarith [hc.1]
  have c2 : 0 ≤ M - u (j - 1) := by linarith [hc.2]
  rw [abs_le]
  unfold stepLine
  constructor
  · nlinarith [mul_nonneg h0 a1, mul_nonneg hw b1, mul_nonneg h0 c1]
  · nlinarith [mul_nonneg h0 a2, mul_nonneg hw b2, mul_nonneg h0 c2]

theorem stepDirichlet_abs_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) {N : ℤ} {u : ℤ → ℝ}
    {M : ℝ} (hu : ∀ j, |u j| ≤ M) (j : ℤ) : |stepDirichlet r N u j| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hu 0)
  unfold stepDirichlet
  split_ifs with hb
  · simpa using hM
  · exact stepLine_abs_le h0 h1 hu j

/-- Stability: the bound survives any number of steps. -/
theorem iterate_stepDirichlet_abs_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) {N : ℤ}
    {u : ℤ → ℝ} {M : ℝ} (hu : ∀ j, |u j| ≤ M) (n : ℕ) :
    ∀ j, |(stepDirichlet r N)^[n] u j| ≤ M := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact stepDirichlet_abs_le h0 h1 ih

/-- Stability turns a per-step defect ε into a global error bound M₀ + n ε. -/
theorem error_accumulation {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) {N : ℤ}
    {e : ℕ → ℤ → ℝ} {M₀ ε : ℝ}
    (hstep : ∀ n j, |e (n + 1) j - stepDirichlet r N (e n) j| ≤ ε)
    (h : ∀ j, |e 0 j| ≤ M₀) (n : ℕ) : ∀ j, |e n j| ≤ M₀ + n * ε := by
  induction n with
  | zero => intro j; simpa using h j
  | succ n ih =>
    intro j
    have h2 := stepDirichlet_abs_le h0 h1 ih j
    have h3 := hstep n j
    calc |e (n + 1) j|
        = |stepDirichlet r N (e n) j + (e (n + 1) j - stepDirichlet r N (e n) j)| := by
          congr 1; ring
      _ ≤ |stepDirichlet r N (e n) j| + |e (n + 1) j - stepDirichlet r N (e n) j| := abs_add _ _
      _ ≤ (M₀ + n * ε) + ε := add_le_add h2 h3
      _ = M₀ + ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- Von Neumann: the mode cos (θ j) is multiplied by 1 + 2 r (cos θ - 1) = 1 - 4 r sin²(θ/2). -/
theorem stepLine_cos_mode (r θ : ℝ) :
    stepLine r (fun j : ℤ => Real.cos (θ * j)) =
      fun j : ℤ => (1 + 2 * r * (Real.cos θ - 1)) * Real.cos (θ * j) := by
  funext j
  have h1 : Real.cos (θ * ((j + 1 : ℤ) : ℝ)) =
      Real.cos (θ * j) * Real.cos θ - Real.sin (θ * j) * Real.sin θ := by
    push_cast
    rw [mul_add, mul_one, Real.cos_add]
  have h2 : Real.cos (θ * ((j - 1 : ℤ) : ℝ)) =
      Real.cos (θ * j) * Real.cos θ + Real.sin (θ * j) * Real.sin θ := by
    push_cast
    rw [mul_sub, mul_one, Real.cos_sub]
  show Real.cos (θ * (j : ℝ)) + r * (Real.cos (θ * ((j + 1 : ℤ) : ℝ))
      - 2 * Real.cos (θ * (j : ℝ)) + Real.cos (θ * ((j - 1 : ℤ) : ℝ)))
    = (1 + 2 * r * (Real.cos θ - 1)) * Real.cos (θ * (j : ℝ))
  rw [h1, h2]
  ring

/-- The zig-zag mode c (-1)^j is an eigenvector with eigenvalue 1 - 4 r. -/
theorem stepLine_zigzag (r c : ℝ) :
    stepLine r (fun j : ℤ => c * (-1 : ℝ) ^ j) =
      fun j : ℤ => c * (1 - 4 * r) * (-1 : ℝ) ^ j := by
  funext j
  have h1 : (-1 : ℝ) ^ (j + 1) = -((-1 : ℝ) ^ j) := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    ring
  have h2 : (-1 : ℝ) ^ (j - 1) = -((-1 : ℝ) ^ j) := by
    rw [zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    norm_num
  show c * (-1 : ℝ) ^ j + r * (c * (-1 : ℝ) ^ (j + 1) - 2 * (c * (-1 : ℝ) ^ j)
      + c * (-1 : ℝ) ^ (j - 1)) = c * (1 - 4 * r) * (-1 : ℝ) ^ j
  rw [h1, h2]
  ring

theorem iterate_stepLine_zigzag (r : ℝ) (n : ℕ) :
    (stepLine r)^[n] (fun j : ℤ => (-1 : ℝ) ^ j) =
      fun j : ℤ => (1 - 4 * r) ^ n * (-1 : ℝ) ^ j := by
  induction n with
  | zero => funext j; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, stepLine_zigzag r ((1 - 4 * r) ^ n)]
    funext j
    ring

/-- Instability: for r > 1/2 the zig-zag mode grows without bound. -/
theorem stepLine_unbounded {r : ℝ} (hr : 1 / 2 < r) (M : ℝ) :
    ∃ n : ℕ, M < |(stepLine r)^[n] (fun j : ℤ => (-1 : ℝ) ^ j) 0| := by
  have h : 1 < |1 - 4 * r| := by
    rw [abs_of_neg (by linarith)]
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
  refine ⟨n, ?_⟩
  rw [iterate_stepLine_zigzag]
  simpa [abs_pow] using hn

end HeatStability
