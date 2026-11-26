/-
Author: Confidence U. Oghosa
Repository: https://github.com/FIddo-tech/MathFormulations
-/

import Mathlib
import HarmonicOscillator

/-!
# The 1D harmonic oscillator: constant energy, existence and uniqueness

Closes the two gaps stated in the paper:
1. the energy is constant on all of ℝ (mean value theorem);
2. the system  x' = v,  v' = -(k/m) x  has exactly one solution for given x(0), v(0)  (m, k > 0).
-/

/-- Energy is constant in time. -/
theorem energy_const (m k : ℝ) (x v : ℝ → ℝ) (hm : m ≠ 0)
    (vx : ∀ t, HasDerivAt x (v t) t)
    (Fma : ∀ t, HasDerivAt v (-(k / m) * x t) t) (s t : ℝ) :
    totalEnergy m k x v t = totalEnergy m k x v s := by
  have hd : ∀ u, HasDerivAt (totalEnergy m k x v) 0 u :=
    fun u => energy_conserved m k x v u vx Fma hm
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t s

/-- Position of the oscillator with angular frequency ω, released with x(0) = x₀, v(0) = v₀. -/
noncomputable def xSol (x₀ v₀ ω t : ℝ) : ℝ :=
  x₀ * Real.cos (ω * t) + (v₀ / ω) * Real.sin (ω * t)

/-- Velocity of the same solution. -/
noncomputable def vSol (x₀ v₀ ω t : ℝ) : ℝ :=
  -(x₀ * ω) * Real.sin (ω * t) + v₀ * Real.cos (ω * t)

theorem hasDerivAt_xSol {ω : ℝ} (hω : ω ≠ 0) (x₀ v₀ t : ℝ) :
    HasDerivAt (xSol x₀ v₀ ω) (vSol x₀ v₀ ω t) t := by
  have h : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hc := (h.cos).const_mul x₀
  have hs := (h.sin).const_mul (v₀ / ω)
  refine (hc.add hs).congr_deriv ?_
  unfold vSol
  first
    | (field_simp; ring)
    | field_simp
    | ring

theorem hasDerivAt_vSol {ω : ℝ} (hω : ω ≠ 0) (x₀ v₀ t : ℝ) :
    HasDerivAt (vSol x₀ v₀ ω) (-(ω ^ 2) * xSol x₀ v₀ ω t) t := by
  have h : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hs := (h.sin).const_mul (-(x₀ * ω))
  have hc := (h.cos).const_mul v₀
  refine (hs.add hc).congr_deriv ?_
  unfold xSol
  first
    | (field_simp; ring)
    | field_simp
    | ring

/-- Existence: for k / m > 0 the explicit formula solves the equations of motion. -/
theorem oscillator_exists {m k : ℝ} (hkm : 0 < k / m) (x₀ v₀ : ℝ) :
    ∃ x v : ℝ → ℝ, (∀ t, HasDerivAt x (v t) t) ∧
      (∀ t, HasDerivAt v (-(k / m) * x t) t) ∧ x 0 = x₀ ∧ v 0 = v₀ := by
  have hω : Real.sqrt (k / m) ≠ 0 := (Real.sqrt_pos.2 hkm).ne'
  have hω2 : Real.sqrt (k / m) ^ 2 = k / m := Real.sq_sqrt hkm.le
  refine ⟨xSol x₀ v₀ (Real.sqrt (k / m)), vSol x₀ v₀ (Real.sqrt (k / m)),
    hasDerivAt_xSol hω x₀ v₀, ?_, ?_, ?_⟩
  · intro t
    simpa [hω2] using hasDerivAt_vSol hω x₀ v₀ t
  · simp [xSol]
  · simp [vSol]

/-- Uniqueness: two solutions with the same initial data agree (m, k > 0). -/
theorem oscillator_unique {m k : ℝ} (hm : 0 < m) (hk : 0 < k) {x₁ v₁ x₂ v₂ : ℝ → ℝ}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : ∀ t, HasDerivAt v₁ (-(k / m) * x₁ t) t)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : ∀ t, HasDerivAt v₂ (-(k / m) * x₂ t) t)
    (h0x : x₁ 0 = x₂ 0) (h0v : v₁ 0 = v₂ 0) (t : ℝ) :
    x₁ t = x₂ t ∧ v₁ t = v₂ t := by
  have hd : ∀ s, HasDerivAt (fun s => x₁ s - x₂ s) (v₁ s - v₂ s) s :=
    fun s => (hx₁ s).sub (hx₂ s)
  have hw : ∀ s, HasDerivAt (fun s => v₁ s - v₂ s) (-(k / m) * (x₁ s - x₂ s)) s := by
    intro s
    have := (hv₁ s).sub (hv₂ s)
    convert this using 1
    ring
  have hE := energy_const m k (fun s => x₁ s - x₂ s) (fun s => v₁ s - v₂ s) hm.ne' hd hw t 0
  have h00 : x₁ 0 - x₂ 0 = 0 := sub_eq_zero.2 h0x
  have h01 : v₁ 0 - v₂ 0 = 0 := sub_eq_zero.2 h0v
  have hE' : (1 / 2 : ℝ) * m * (v₁ t - v₂ t) ^ 2 + (1 / 2) * k * (x₁ t - x₂ t) ^ 2 = 0 := by
    have h := hE
    simp only [totalEnergy] at h
    rw [h00, h01] at h
    first | linarith | nlinarith [h]
  have hA : 0 ≤ m * (v₁ t - v₂ t) ^ 2 := by positivity
  have hB : 0 ≤ k * (x₁ t - x₂ t) ^ 2 := by positivity
  have hA0 : m * (v₁ t - v₂ t) ^ 2 = 0 := by linarith
  have hB0 : k * (x₁ t - x₂ t) ^ 2 = 0 := by linarith
  have hv : v₁ t - v₂ t = 0 :=
    (pow_eq_zero_iff two_ne_zero).1 ((mul_eq_zero.1 hA0).resolve_left hm.ne')
  have hx : x₁ t - x₂ t = 0 :=
    (pow_eq_zero_iff two_ne_zero).1 ((mul_eq_zero.1 hB0).resolve_left hk.ne')
  exact ⟨sub_eq_zero.1 hx, sub_eq_zero.1 hv⟩

/-- Every solution is the explicit cosine/sine formula. -/
theorem oscillator_eq_xSol {m k : ℝ} (hm : 0 < m) (hk : 0 < k) {x v : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (-(k / m) * x t) t) (t : ℝ) :
    x t = xSol (x 0) (v 0) (Real.sqrt (k / m)) t := by
  have hkm : 0 < k / m := div_pos hk hm
  have hω : Real.sqrt (k / m) ≠ 0 := (Real.sqrt_pos.2 hkm).ne'
  have hω2 : Real.sqrt (k / m) ^ 2 = k / m := Real.sq_sqrt hkm.le
  have key := oscillator_unique hm hk hx hv
    (fun s => hasDerivAt_xSol hω (x 0) (v 0) s)
    (fun s => by simpa [hω2] using hasDerivAt_vSol hω (x 0) (v 0) s)
    (by simp [xSol]) (by simp [vSol]) t
  exact key.1
