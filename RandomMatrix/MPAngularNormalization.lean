import RandomMatrix.MPTrigNormalization

/-! The continuous MP mass, including the singular endpoint at aspect ratio one. -/

open Set Real intervalIntegral
open MeasureTheory (volume ae_of_all)

namespace RandomMatrix

noncomputable def mpAngularWeight (γ t : ℝ) : ℝ :=
  (2 / Real.pi) * (Real.sin t ^ 2 / mpAngle γ t)

theorem mpLower_pos {γ : ℝ} (hγ : 0 < γ) (hne : γ ≠ 1) : 0 < mpLower γ := by
  apply sq_pos_of_ne_zero
  intro h
  have hs : Real.sqrt γ = 1 := by linarith
  have hsq := Real.sq_sqrt hγ.le
  rw [hs] at hsq
  exact hne (by linarith)

theorem mpAngle_pos_of_ne_one {γ : ℝ} (hγ : 0 < γ) (hne : γ ≠ 1) (t : ℝ) :
    0 < mpAngle γ t := by
  have hl := mpLower_pos hγ hne
  rw [mpLower_eq hγ.le] at hl
  dsimp [mpAngle]
  have hr : 0 < 2 * Real.sqrt γ := by positivity
  nlinarith [Real.cos_le_one t]

theorem mpAngularWeight_one {t : ℝ} (ht : t ∈ Ioc 0 Real.pi) :
    mpAngularWeight 1 t = (1 + Real.cos t) / Real.pi := by
  have hc : Real.cos t < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      ⟨le_rfl, Real.pi_pos.le⟩ ⟨ht.1.le, ht.2⟩ ht.1
  have hd : 2 - 2 * Real.cos t ≠ 0 := by linarith
  simp only [mpAngularWeight, mpAngle, Real.sqrt_one]
  norm_num
  field_simp [sub_ne_zero.mpr hc.ne']
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem mpAngularWeight_integrable {γ : ℝ} (hγ : 0 < γ) :
    IntervalIntegrable (mpAngularWeight γ) volume 0 Real.pi := by
  by_cases hne : γ = 1
  · subst γ
    have hi : IntervalIntegrable (fun t => (1 + Real.cos t) / Real.pi) volume 0 Real.pi :=
      (by fun_prop : Continuous (fun t => (1 + Real.cos t) / Real.pi)).intervalIntegrable _ _
    apply hi.congr
    intro t ht
    rw [uIoc_of_le Real.pi_pos.le] at ht
    exact (mpAngularWeight_one ht).symm
  · have hc : Continuous (mpAngularWeight γ) := by
      unfold mpAngularWeight
      exact continuous_const.mul ((Real.continuous_sin.pow 2).div (mpAngle_continuous γ)
        (fun t => (mpAngle_pos_of_ne_one hγ hne t).ne'))
    exact hc.intervalIntegrable _ _

private theorem mpAngle_reciprocal_integral {γ : ℝ} (hγ : 0 < γ) (hne : γ ≠ 1) :
    (∫ t in 0..Real.pi, 1 / mpAngle γ t) = Real.pi / |γ - 1| := by
  have hm : 0 < 1 + γ - 2 * Real.sqrt γ := by
    rw [← mpLower_eq hγ.le]
    exact mpLower_pos hγ hne
  have hp : 0 < 1 + γ + 2 * Real.sqrt γ := by positivity
  have hprod : Real.sqrt (1 + γ - 2 * Real.sqrt γ) *
      Real.sqrt (1 + γ + 2 * Real.sqrt γ) = |γ - 1| := by
    rw [← Real.sqrt_mul hm.le]
    have he : (1 + γ - 2 * Real.sqrt γ) * (1 + γ + 2 * Real.sqrt γ) =
        (γ - 1) ^ 2 := by nlinarith [Real.sq_sqrt hγ.le]
    rw [he, Real.sqrt_sq_eq_abs]
  simpa only [mpAngle, hprod] using integral_inv_affine_cos hm hp

private theorem mpAngularWeight_integral_regular {γ : ℝ} (hγ : 0 < γ) (hne : γ ≠ 1) :
    (∫ t in 0..Real.pi, mpAngularWeight γ t) = (1 + γ - |γ - 1|) / (2 * γ) := by
  have he (t : ℝ) : mpAngularWeight γ t =
      1 / (2 * Real.pi * γ) *
        ((1 + γ) + 2 * Real.sqrt γ * Real.cos t - (γ - 1) ^ 2 * (1 / mpAngle γ t)) := by
    have hx := (mpAngle_pos_of_ne_one hγ hne t).ne'
    unfold mpAngularWeight
    field_simp
    dsimp [mpAngle]
    linear_combination 4 * Real.sqrt γ ^ 2 * (Real.sin_sq_add_cos_sq t) +
      (4 - 4 * Real.sin t ^ 2) * (Real.sq_sqrt hγ.le)
  have hi : IntervalIntegrable (fun t => 1 / mpAngle γ t) volume 0 Real.pi :=
    (continuous_const.div (mpAngle_continuous γ)
      (fun t => (mpAngle_pos_of_ne_one hγ hne t).ne')).intervalIntegrable _ _
  simp_rw [he]
  rw [integral_const_mul, integral_sub, integral_add]
  · rw [integral_const, integral_const_mul, integral_cos,
      integral_const_mul, mpAngle_reciprocal_integral hγ hne]
    simp only [Real.sin_pi, Real.sin_zero, sub_self, mul_zero, add_zero, sub_zero, smul_eq_mul]
    have habs : |γ - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
    have hsq : |γ - 1| ^ 2 = (γ - 1) ^ 2 := sq_abs _
    field_simp
    nlinarith [hsq]
  · exact intervalIntegral.intervalIntegrable_const
  · exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  · exact intervalIntegral.intervalIntegrable_const.add ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _)
  · exact hi.const_mul _

/-- The continuous part has exactly the mass missing from the required zero atom. -/
theorem mpAngularWeight_integral {γ : ℝ} (hγ : 0 < γ) :
    (∫ t in 0..Real.pi, mpAngularWeight γ t) = min 1 (1 / γ) := by
  by_cases hne : γ = 1
  · subst γ
    have he : (∫ t in 0..Real.pi, mpAngularWeight 1 t) =
        ∫ t in 0..Real.pi, (1 + Real.cos t) / Real.pi := by
      apply integral_congr_ae
      apply ae_of_all
      intro t ht
      rw [uIoc_of_le Real.pi_pos.le] at ht
      exact mpAngularWeight_one ht
    rw [he, integral_div, integral_add intervalIntegral.intervalIntegrable_const (Real.continuous_cos.intervalIntegrable _ _)]
    simp [integral_const, integral_cos, Real.pi_ne_zero]
  · rw [mpAngularWeight_integral_regular hγ hne]
    by_cases hle : γ ≤ 1
    · rw [abs_of_nonpos (by linarith), min_eq_left ((le_div_iff₀ hγ).mpr (by linarith))]
      field_simp
      ring
    · have hge : 1 ≤ γ := (le_of_not_ge hle)
      rw [abs_of_nonneg (by linarith), min_eq_right ((div_le_iff₀ hγ).mpr (by linarith))]
      field_simp
      ring

end RandomMatrix
