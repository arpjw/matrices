import RandomMatrix.MPAngularNormalization
import RandomMatrix.MPMomentRecurrence
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Change of variables for the actual MP density and all its Lebesgue moments. -/

open Set MeasureTheory Real

namespace RandomMatrix

theorem mpAngle_image_open {γ : ℝ} (hγ : 0 < γ) :
    mpAngle γ '' Ioo 0 Real.pi = Ioo (mpLower γ) (mpUpper γ) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact mpAngle_mem hγ ht
  · intro hx
    have hxclosed : x ∈ mpAngle γ '' Icc 0 Real.pi := by
      rw [mpAngle_image hγ]
      exact ⟨hx.1.le, hx.2.le⟩
    obtain ⟨t, ht, he⟩ := hxclosed
    have ht0 : t ≠ 0 := by
      intro h
      subst t
      rw [mpAngle_zero hγ.le] at he
      exact (ne_of_lt hx.1) he
    have htπ : t ≠ Real.pi := by
      intro h
      subst t
      rw [mpAngle_pi hγ.le] at he
      exact (ne_of_lt hx.2) he.symm
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 htπ⟩, he⟩

/-- The Jacobian cancels the square root in the continuous density. -/
theorem mpDensity_jacobian {γ t : ℝ} (hγ : 0 < γ) (ht : t ∈ Ioo 0 Real.pi) :
    |2 * Real.sqrt γ * Real.sin t| * mpDensity γ (mpAngle γ t) = mpAngularWeight γ t := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hx := (mpAngle_pos hγ ht).ne'
  rw [abs_of_pos (by positivity), mpDensity, if_pos (mpAngle_mem hγ ht),
    mpAngle_sqrt hγ.le ⟨ht.1.le, ht.2.le⟩]
  unfold mpAngularWeight
  field_simp
  nlinarith [Real.sq_sqrt hγ.le]

private theorem mpDensity_mul_indicator (γ : ℝ) (f : ℝ → ℝ) :
    (Ioo (mpLower γ) (mpUpper γ)).indicator (fun x => f x * mpDensity γ x) =
      (fun x => f x * mpDensity γ x) := by
  funext x
  by_cases hx : x ∈ Ioo (mpLower γ) (mpUpper γ)
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx]
    simp only [mpDensity, if_neg hx, mul_zero]

/-- Change of variables for any real test function, without an assumed integral formula. -/
theorem mpDensity_integral_change {γ : ℝ} (hγ : 0 < γ) (f : ℝ → ℝ) :
    (∫ x, f x * mpDensity γ x) =
      ∫ t in 0..Real.pi, f (mpAngle γ t) * mpAngularWeight γ t := by
  rw [← mpDensity_mul_indicator γ f, integral_indicator measurableSet_Ioo,
    ← mpAngle_image_open hγ]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (mpAngle_hasDerivAt γ t).hasDerivWithinAt)
    ((mpAngle_strictMonoOn hγ).mono Ioo_subset_Icc_self).injOn]
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  simp only [smul_eq_mul]
  calc
    _ = f (mpAngle γ t) * (|2 * Real.sqrt γ * Real.sin t| * mpDensity γ (mpAngle γ t)) := by ring
    _ = _ := by rw [mpDensity_jacobian hγ ht]

/-- Integrability is also transferred by the injective differentiable substitution. -/
theorem mpDensity_integrable_iff {γ : ℝ} (hγ : 0 < γ) (f : ℝ → ℝ) :
    Integrable (fun x => f x * mpDensity γ x) ↔
      IntervalIntegrable (fun t => f (mpAngle γ t) * mpAngularWeight γ t) volume 0 Real.pi := by
  rw [← mpDensity_mul_indicator γ f, integrable_indicator_iff measurableSet_Ioo,
    ← mpAngle_image_open hγ]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (mpAngle_hasDerivAt γ t).hasDerivWithinAt)
    ((mpAngle_strictMonoOn hγ).mono Ioo_subset_Icc_self).injOn]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le]
  apply integrableOn_congr_fun _ measurableSet_Ioo
  intro t ht
  simp only [smul_eq_mul]
  calc
    _ = f (mpAngle γ t) * (|2 * Real.sqrt γ * Real.sin t| * mpDensity γ (mpAngle γ t)) := by ring
    _ = _ := by rw [mpDensity_jacobian hγ ht]

theorem mpDensity_integrable {γ : ℝ} (hγ : 0 < γ) : Integrable (mpDensity γ) := by
  simpa only [one_mul] using (mpDensity_integrable_iff hγ (fun _ => 1)).mpr
    (by simpa only [one_mul] using mpAngularWeight_integrable hγ)

/-- Exact normalization of the continuous part, with its loss of mass when gamma > 1. -/
theorem mpDensity_integral {γ : ℝ} (hγ : 0 < γ) :
    (∫ x, mpDensity γ x) = min 1 (1 / γ) := by
  have h := mpDensity_integral_change hγ (fun _ => 1)
  simpa only [one_mul, mpAngularWeight_integral hγ] using h

private theorem mpAngular_positive_moment {γ t : ℝ} (hγ : 0 < γ)
    (ht : t ∈ Ioc 0 Real.pi) (k : ℕ) :
    mpAngle γ t ^ (k + 1) * mpAngularWeight γ t =
      2 / Real.pi * (mpAngle γ t ^ k * Real.sin t ^ 2) := by
  by_cases htπ : t = Real.pi
  · subst t
    simp [mpAngularWeight]
  · have hx := (mpAngle_pos hγ ⟨ht.1, lt_of_le_of_ne ht.2 htπ⟩).ne'
    unfold mpAngularWeight
    rw [pow_succ]
    field_simp

/-- Every density moment is integrable, including the mass integral. -/
theorem mpDensity_moment_integrable (k : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun x => x ^ k * mpDensity γ x) := by
  cases k with
  | zero => simpa using mpDensity_integrable hγ
  | succ k =>
    apply (mpDensity_integrable_iff hγ _).mpr
    apply ((mpAngular_integrable k γ).const_mul (2 / Real.pi)).congr
    intro t ht
    rw [uIoc_of_le Real.pi_pos.le] at ht
    exact (mpAngular_positive_moment hγ ht k).symm

/-- Every positive moment of the explicit density is the Narayana polynomial. -/
theorem mpDensity_moment_succ (k : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    (∫ x, x ^ (k + 1) * mpDensity γ x) = mpMoment (k + 1) γ := by
  rw [mpDensity_integral_change hγ]
  calc
    _ = ∫ t in 0..Real.pi, 2 / Real.pi * (mpAngle γ t ^ k * Real.sin t ^ 2) := by
      apply intervalIntegral.integral_congr_ae
      apply ae_of_all
      intro t ht
      rw [uIoc_of_le Real.pi_pos.le] at ht
      exact mpAngular_positive_moment hγ ht k
    _ = mpAngularMoment k γ := by rw [intervalIntegral.integral_const_mul]; rfl
    _ = mpMoment (k + 1) γ := mpAngularMoment_eq_mpMoment k hγ

end RandomMatrix
