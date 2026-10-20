import RandomMatrix.MPParameters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! An elementary trigonometric integral used to normalize the MP density. -/

open Set Real intervalIntegral
open MeasureTheory (volume)

namespace RandomMatrix

private theorem quadratic_trig_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (t : ℝ) :
    0 < u ^ 2 * Real.cos t ^ 2 + v ^ 2 * Real.sin t ^ 2 := by
  by_cases hc : Real.cos t = 0
  · have hs : Real.sin t ^ 2 = 1 := by simpa [hc] using Real.sin_sq_add_cos_sq t
    simp [hc, hs, sq_pos_of_pos hv]
  · have hc2 : 0 < Real.cos t ^ 2 := sq_pos_of_ne_zero hc
    positivity

private theorem quadratic_trig_continuous {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Continuous (fun t => 1 / (u ^ 2 * Real.cos t ^ 2 + v ^ 2 * Real.sin t ^ 2)) :=
  continuous_const.div (by fun_prop) (fun t => (quadratic_trig_pos hu hv t).ne')

private theorem integral_quadratic_trig_quarter {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t in 0..Real.pi / 4, 1 / (u ^ 2 * Real.cos t ^ 2 + v ^ 2 * Real.sin t ^ 2)) =
      Real.arctan (v / u) / (u * v) := by
  let F := fun t => (1 / (u * v)) * Real.arctan ((v / u) * Real.tan t)
  have hD (t : ℝ) (ht : t ∈ uIcc 0 (Real.pi / 4)) :
      HasDerivAt F (1 / (u ^ 2 * Real.cos t ^ 2 + v ^ 2 * Real.sin t ^ 2)) t := by
    rw [uIcc_of_le (by positivity)] at ht
    have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], by linarith [Real.pi_pos, ht.2]⟩).ne'
    have h := (((Real.hasDerivAt_tan hc).const_mul (v / u)).arctan).const_mul (1 / (u * v))
    convert h using 1
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have h := integral_eq_sub_of_hasDerivAt hD
    ((quadratic_trig_continuous hu hv).intervalIntegrable _ _)
  simp only [F, Real.tan_pi_div_four, Real.tan_zero, mul_one, mul_zero, Real.arctan_zero,
    sub_zero] at h
  convert h using 1
  ring

/-- The reciprocal of a positive quadratic form on the unit circle. -/
theorem integral_quadratic_trig {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t in 0..Real.pi / 2, 1 / (u ^ 2 * Real.cos t ^ 2 + v ^ 2 * Real.sin t ^ 2)) =
      Real.pi / (2 * u * v) := by
  let f := fun t => 1 / (u ^ 2 * Real.cos t ^ 2 + v ^ 2 * Real.sin t ^ 2)
  have hc := quadratic_trig_continuous hu hv
  have hsplit := integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (Real.pi / 4)) (hc.intervalIntegrable (Real.pi / 4) (Real.pi / 2))
  have hsecond : (∫ t in Real.pi / 4..Real.pi / 2, f t) =
      Real.arctan (u / v) / (v * u) := by
    have hsub := integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 4) f (Real.pi / 2)
    have he : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    rw [he, sub_zero] at hsub
    rw [← hsub]
    simp only [f, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    simpa only [add_comm] using integral_quadratic_trig_quarter hv hu
  change (∫ t in 0..Real.pi / 2, f t) = _
  rw [← hsplit, integral_quadratic_trig_quarter hu hv, hsecond]
  have hi : u / v = (v / u)⁻¹ := by simp
  rw [hi, Real.arctan_inv_of_pos (div_pos hv hu)]
  field_simp
  ring

/-- Reciprocal affine cosine integral, proved from the quadratic trigonometric integral. -/
theorem integral_inv_affine_cos {c r : ℝ} (hm : 0 < c - r) (hp : 0 < c + r) :
    (∫ t in 0..Real.pi, 1 / (c - r * Real.cos t)) =
      Real.pi / (Real.sqrt (c - r) * Real.sqrt (c + r)) := by
  have he (t : ℝ) : c - r * Real.cos t =
      Real.sqrt (c - r) ^ 2 * Real.cos (t / 2) ^ 2 +
      Real.sqrt (c + r) ^ 2 * Real.sin (t / 2) ^ 2 := by
    rw [Real.sq_sqrt hm.le, Real.sq_sqrt hp.le]
    have hc := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at hc
    linear_combination -(c + r) * (Real.sin_sq_add_cos_sq (t / 2)) - r * hc
  simp_rw [he]
  rw [integral_comp_div (fun t => 1 / (Real.sqrt (c - r) ^ 2 * Real.cos t ^ 2 +
    Real.sqrt (c + r) ^ 2 * Real.sin t ^ 2)) (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zero_div, smul_eq_mul]
  rw [integral_quadratic_trig (Real.sqrt_pos.mpr hm) (Real.sqrt_pos.mpr hp)]
  ring

end RandomMatrix
