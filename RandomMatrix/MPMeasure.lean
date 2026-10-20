import RandomMatrix.MPDensityIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support

/-! The explicit Marchenko-Pastur probability measure, its atom, support, and all moments. -/

open Set MeasureTheory
open scoped ENNReal

namespace RandomMatrix

noncomputable def mpContinuousMeasure (γ : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (mpDensity γ x))

/-- The MP law in the convention gamma = p/n and S = XX^T/n. -/
noncomputable def marchenkoPastur (γ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (mpAtom γ) • Measure.dirac 0 + mpContinuousMeasure γ

theorem mpAtom_nonneg (γ : ℝ) : 0 ≤ mpAtom γ := le_max_right _ _

theorem mpAtom_add_continuous_mass (γ : ℝ) : mpAtom γ + min 1 (1 / γ) = 1 := by
  unfold mpAtom
  by_cases h : 1 / γ ≤ 1
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_left (le_of_not_ge h), max_eq_right (by linarith)]
    ring

/-- The mass calculation for the continuous measure uses the proved density integral. -/
theorem mpContinuousMeasure_mass {γ : ℝ} (hγ : 0 < γ) :
    mpContinuousMeasure γ Set.univ = ENNReal.ofReal (min 1 (1 / γ)) := by
  rw [mpContinuousMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (mpDensity_integrable hγ)
      (ae_of_all _ (mpDensity_nonneg hγ)), mpDensity_integral hγ]

/-- Normalization is proved for every positive real aspect ratio, including one. -/
theorem marchenkoPastur_isProbabilityMeasure {γ : ℝ} (hγ : 0 < γ) :
    IsProbabilityMeasure (marchenkoPastur γ) := by
  constructor
  rw [marchenkoPastur, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ 0), smul_eq_mul, mul_one,
    mpContinuousMeasure_mass hγ, ← ENNReal.ofReal_add (mpAtom_nonneg γ)
      (le_min (by norm_num) (by positivity)), mpAtom_add_continuous_mass]
  simp

noncomputable def mpProbabilityMeasure (γ : ℝ) (hγ : 0 < γ) : ProbabilityMeasure ℝ :=
  ⟨marchenkoPastur γ, marchenkoPastur_isProbabilityMeasure hγ⟩

@[simp] theorem mpProbabilityMeasure_coe (γ : ℝ) (hγ : 0 < γ) :
    (mpProbabilityMeasure γ hγ : Measure ℝ) = marchenkoPastur γ := rfl

/-- The continuous part is atomless, so the full atom at zero is exactly the displayed weight. -/
theorem marchenkoPastur_zero_atom (γ : ℝ) :
    marchenkoPastur γ {0} = ENNReal.ofReal (mpAtom γ) := by
  simp [marchenkoPastur, mpContinuousMeasure]

theorem marchenkoPastur_zero_atom_real (γ : ℝ) :
    (marchenkoPastur γ {0}).toReal = max (1 - 1 / γ) 0 := by
  rw [marchenkoPastur_zero_atom, ENNReal.toReal_ofReal (mpAtom_nonneg γ)]
  rfl

/-- Integration against the continuous part is ordinary density integration. -/
theorem mpContinuousMeasure_integral {γ : ℝ} (hγ : 0 < γ) (f : ℝ → ℝ) :
    (∫ x, f x ∂mpContinuousMeasure γ) = ∫ x, f x * mpDensity γ x := by
  rw [mpContinuousMeasure, integral_withDensity_eq_integral_toReal_smul
    ((mpDensity_measurable γ).ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (mpDensity_nonneg hγ _), smul_eq_mul, mul_comm]

theorem mpContinuousMeasure_moment_integrable (k : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun x : ℝ => x ^ k) (mpContinuousMeasure γ) := by
  rw [mpContinuousMeasure, integrable_withDensity_iff_integrable_smul'
    ((mpDensity_measurable γ).ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (mpDensity_nonneg hγ _), smul_eq_mul, mul_comm] using
    mpDensity_moment_integrable k hγ

/-- Every natural moment is integrable for the full law. -/
theorem marchenkoPastur_moment_integrable (k : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (fun x : ℝ => x ^ k) (marchenkoPastur γ) := by
  rw [marchenkoPastur, integrable_add_measure]
  exact ⟨(integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top,
    mpContinuousMeasure_moment_integrable k hγ⟩

/-- All moments of the explicit density plus atom equal the proved Narayana formula.
Order zero includes the atom and equals one. Positive powers vanish at the atom. -/
theorem marchenkoPastur_moment (k : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    (∫ x, x ^ k ∂marchenkoPastur γ) = mpMoment k γ := by
  cases k with
  | zero =>
    letI := marchenkoPastur_isProbabilityMeasure hγ
    simp
  | succ k =>
    rw [marchenkoPastur, integral_add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
      (mpContinuousMeasure_moment_integrable (k + 1) hγ), integral_smul_measure,
      integral_dirac, mpContinuousMeasure_integral hγ, mpDensity_moment_succ k hγ]
    simp

private theorem mpDensity_zero_outside {γ x : ℝ} (hx : x ∉ Icc 0 (mpUpper γ)) :
    mpDensity γ x = 0 := by
  unfold mpDensity
  apply if_neg
  intro h
  exact hx ⟨le_trans (mpLower_nonneg γ) h.1.le, h.2.le⟩

theorem marchenkoPastur_compl_support_interval (γ : ℝ) :
    marchenkoPastur γ (Icc 0 (mpUpper γ))ᶜ = 0 := by
  have hzero : (0 : ℝ) ∈ Icc 0 (mpUpper γ) := ⟨le_rfl, sq_nonneg _⟩
  rw [marchenkoPastur, Measure.add_apply,
    Measure.smul_apply]
  have hd : Measure.dirac (0 : ℝ) (Icc 0 (mpUpper γ))ᶜ = 0 := by
    simp [hzero]
  rw [hd, smul_zero, zero_add, mpContinuousMeasure,
    withDensity_apply _ isClosed_Icc.measurableSet.compl]
  calc
    _ = ∫⁻ _ in (Icc 0 (mpUpper γ))ᶜ, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet.compl] with x hx
      rw [mpDensity_zero_outside hx, ENNReal.ofReal_zero]
    _ = 0 := by simp

/-- Compact, nonnegative support for the full density-plus-atom law. -/
theorem marchenkoPastur_support_subset (γ : ℝ) :
    (marchenkoPastur γ).support ⊆ Icc 0 (mpUpper γ) :=
  Measure.support_subset_of_isClosed isClosed_Icc (marchenkoPastur_compl_support_interval γ)

theorem marchenkoPastur_support_compact (γ : ℝ) : IsCompact (marchenkoPastur γ).support :=
  isCompact_Icc.of_isClosed_subset Measure.isClosed_support (marchenkoPastur_support_subset γ)

end RandomMatrix
