import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.LinearCombination

/-! The endpoints, density, and angular parametrization of the MP measure. -/

open Set MeasureTheory Real

namespace RandomMatrix

noncomputable def mpLower (γ : ℝ) : ℝ := (1 - Real.sqrt γ) ^ 2
noncomputable def mpUpper (γ : ℝ) : ℝ := (1 + Real.sqrt γ) ^ 2
noncomputable def mpAngle (γ t : ℝ) : ℝ := 1 + γ - 2 * Real.sqrt γ * Real.cos t

/-- The continuous MP density, zero outside the open spectral interval. -/
noncomputable def mpDensity (γ x : ℝ) : ℝ :=
  if x ∈ Ioo (mpLower γ) (mpUpper γ) then
    Real.sqrt ((mpUpper γ - x) * (x - mpLower γ)) / (2 * Real.pi * γ * x)
  else 0

/-- The atom required by the p-by-n covariance convention. -/
noncomputable def mpAtom (γ : ℝ) : ℝ := max (1 - 1 / γ) 0

theorem mpLower_nonneg (γ : ℝ) : 0 ≤ mpLower γ := sq_nonneg _

theorem mpLower_eq {γ : ℝ} (hγ : 0 ≤ γ) :
    mpLower γ = 1 + γ - 2 * Real.sqrt γ := by
  unfold mpLower
  nlinarith [Real.sq_sqrt hγ]

theorem mpUpper_eq {γ : ℝ} (hγ : 0 ≤ γ) :
    mpUpper γ = 1 + γ + 2 * Real.sqrt γ := by
  unfold mpUpper
  nlinarith [Real.sq_sqrt hγ]

theorem mpLower_lt_upper {γ : ℝ} (hγ : 0 < γ) : mpLower γ < mpUpper γ := by
  rw [mpLower_eq hγ.le, mpUpper_eq hγ.le]
  linarith [Real.sqrt_pos.mpr hγ]

@[simp] theorem mpAngle_zero {γ : ℝ} (hγ : 0 ≤ γ) : mpAngle γ 0 = mpLower γ := by
  simp [mpAngle, mpLower_eq hγ]

@[simp] theorem mpAngle_pi {γ : ℝ} (hγ : 0 ≤ γ) : mpAngle γ Real.pi = mpUpper γ := by
  simp [mpAngle, mpUpper_eq hγ]

@[fun_prop] theorem mpAngle_continuous (γ : ℝ) : Continuous (mpAngle γ) := by
  unfold mpAngle
  fun_prop

theorem mpAngle_hasDerivAt (γ t : ℝ) :
    HasDerivAt (mpAngle γ) (2 * Real.sqrt γ * Real.sin t) t := by
  convert (hasDerivAt_const t (1 + γ)).sub
    ((Real.hasDerivAt_cos t).const_mul (2 * Real.sqrt γ)) using 1
  simp

theorem mpAngle_strictMonoOn {γ : ℝ} (hγ : 0 < γ) :
    StrictMonoOn (mpAngle γ) (Icc 0 Real.pi) := by
  intro x hx y hy hxy
  have hcos := Real.strictAntiOn_cos hx hy hxy
  have hr : 0 < 2 * Real.sqrt γ := by positivity
  dsimp [mpAngle]
  nlinarith

theorem mpAngle_image {γ : ℝ} (hγ : 0 < γ) :
    mpAngle γ '' Icc 0 Real.pi = Icc (mpLower γ) (mpUpper γ) := by
  simpa only [mpAngle_zero hγ.le, mpAngle_pi hγ.le] using
    (mpAngle_continuous γ).continuousOn.image_Icc_of_monotoneOn Real.pi_pos.le
      (mpAngle_strictMonoOn hγ).monotoneOn

theorem mpAngle_mem {γ t : ℝ} (hγ : 0 < γ) (ht : t ∈ Ioo 0 Real.pi) :
    mpAngle γ t ∈ Ioo (mpLower γ) (mpUpper γ) := by
  have hm := mpAngle_strictMonoOn hγ
  constructor
  · simpa only [mpAngle_zero hγ.le] using
      hm ⟨le_rfl, Real.pi_pos.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
  · simpa only [mpAngle_pi hγ.le] using
      hm ⟨ht.1.le, ht.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ ht.2

theorem mpAngle_pos {γ t : ℝ} (hγ : 0 < γ) (ht : t ∈ Ioo 0 Real.pi) :
    0 < mpAngle γ t := lt_of_le_of_lt (mpLower_nonneg γ) (mpAngle_mem hγ ht).1

theorem mpAngle_sqrt {γ t : ℝ} (hγ : 0 ≤ γ) (ht : t ∈ Icc 0 Real.pi) :
    Real.sqrt ((mpUpper γ - mpAngle γ t) * (mpAngle γ t - mpLower γ)) =
      2 * Real.sqrt γ * Real.sin t := by
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ht
  have he : (mpUpper γ - mpAngle γ t) * (mpAngle γ t - mpLower γ) =
      (2 * Real.sqrt γ * Real.sin t) ^ 2 := by
    rw [mpUpper_eq hγ, mpLower_eq hγ]
    dsimp [mpAngle]
    linear_combination -4 * Real.sqrt γ ^ 2 * (Real.sin_sq_add_cos_sq t)
  rw [he, Real.sqrt_sq (by positivity)]

@[fun_prop] theorem mpDensity_measurable (γ : ℝ) : Measurable (mpDensity γ) := by
  unfold mpDensity
  apply Measurable.ite measurableSet_Ioo <;> fun_prop

theorem mpDensity_nonneg {γ : ℝ} (hγ : 0 < γ) (x : ℝ) : 0 ≤ mpDensity γ x := by
  unfold mpDensity
  split_ifs with hx
  · have hx0 : 0 < x := lt_of_le_of_lt (mpLower_nonneg γ) hx.1
    positivity
  · rfl

end RandomMatrix
