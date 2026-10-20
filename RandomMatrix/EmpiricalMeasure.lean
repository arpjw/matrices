import RandomMatrix.SpectralGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support

/-! The empirical eigenvalue measure of a real sample covariance matrix. -/

open MeasureTheory
open scoped ENNReal

namespace RandomMatrix

/-- Every eigenvalue receives weight `1 / p`, including repeated and zero eigenvalues. -/
noncomputable def empiricalMeasure {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) : Measure ℝ :=
  ENNReal.ofReal (p : ℝ)⁻¹ • ∑ i, Measure.dirac (covarianceEigenvalues X i)

/-- A direct counting formula for the empirical measure of any measurable set. -/
theorem empiricalMeasure_apply {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    empiricalMeasure X s = ENNReal.ofReal (p : ℝ)⁻¹ *
      (Nat.card {i : Fin p // covarianceEigenvalues X i ∈ s} : ℝ≥0∞) := by
  classical
  simp [empiricalMeasure, Measure.finset_sum_apply, hs,
    Set.indicator_apply, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Positive row dimension makes the empirical measure a probability measure. -/
theorem empiricalMeasure_isProbabilityMeasure {p n : ℕ} (hp : 0 < p)
    (X : Matrix (Fin p) (Fin n) ℝ) : IsProbabilityMeasure (empiricalMeasure X) := by
  constructor
  rw [empiricalMeasure_apply X Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, Nat.card_eq_fintype_card, Fintype.card_subtype_true,
    Fintype.card_fin]
  rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hp)]
  simp only [ENNReal.ofReal_natCast]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') (by simp)

/-- The bundled measure uses mathlib's topology of weak convergence of probabilities. -/
noncomputable def empiricalProbabilityMeasure {p n : ℕ} (hp : 0 < p)
    (X : Matrix (Fin p) (Fin n) ℝ) : ProbabilityMeasure ℝ :=
  ⟨empiricalMeasure X, empiricalMeasure_isProbabilityMeasure hp X⟩

@[simp] theorem empiricalProbabilityMeasure_coe {p n : ℕ} (hp : 0 < p)
    (X : Matrix (Fin p) (Fin n) ℝ) :
    (empiricalProbabilityMeasure hp X : Measure ℝ) = empiricalMeasure X := rfl

/-- Finite spectral measures integrate every real-valued function. -/
theorem empiricalMeasure_integrable {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (f : ℝ → ℝ) : Integrable f (empiricalMeasure X) := by
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  exact integrable_finset_sum_measure.mpr fun _ _ => integrable_dirac (by simp)

/-- Integration is the average over the entire eigenvalue list. -/
theorem empiricalMeasure_integral {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂empiricalMeasure X = (p : ℝ)⁻¹ * ∑ i, f (covarianceEigenvalues X i) := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac (by simp))]
  simp [ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg p))]

/-- The spectral moment is exactly the normalized trace moment, also for `k = 0`. -/
theorem empiricalMeasure_moment {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) (k : ℕ) :
    ∫ x, x ^ k ∂empiricalMeasure X = normalizedMoment X k := by
  rw [empiricalMeasure_integral, normalizedMoment, covariance_trace_pow]

/-- Order zero records the full unit mass. -/
theorem empiricalMeasure_moment_zero {p n : ℕ} (hp : 0 < p)
    (X : Matrix (Fin p) (Fin n) ℝ) : ∫ x, x ^ 0 ∂empiricalMeasure X = 1 := by
  rw [empiricalMeasure_integral]
  simp [ne_of_gt hp]

/-- The measure gives no mass to negative eigenvalues. -/
theorem empiricalMeasure_negative {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    empiricalMeasure X (Set.Iio 0) = 0 := by
  rw [empiricalMeasure_apply X _ measurableSet_Iio]
  haveI : IsEmpty {i : Fin p // covarianceEigenvalues X i ∈ Set.Iio 0} :=
    ⟨fun i => (not_lt_of_ge (covariance_eigenvalues_nonneg X i.val)) i.property⟩
  have hcard : Nat.card {i : Fin p // covarianceEigenvalues X i ∈ Set.Iio 0} = 0 :=
    Nat.card_eq_zero.mpr (Or.inl inferInstance)
  rw [hcard]
  simp

/-- Almost every spectral point is nonnegative. -/
theorem empiricalMeasure_ae_nonneg {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    ∀ᵐ x ∂empiricalMeasure X, 0 ≤ x := by
  rw [ae_iff]
  simpa using empiricalMeasure_negative X

/-- The atom at zero is exactly the fraction of zero eigenvalues. -/
theorem empiricalMeasure_zero_atom {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    empiricalMeasure X {0} = ENNReal.ofReal (p : ℝ)⁻¹ *
      (Nat.card {i : Fin p // covarianceEigenvalues X i = 0} : ℝ≥0∞) := by
  simpa using empiricalMeasure_apply X {0} (measurableSet_singleton 0)

/-- In real units, the atom at zero is the normalized nullity. -/
theorem empiricalMeasure_zero_atom_real {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    (empiricalMeasure X {0}).toReal =
      (Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (covariance X))) : ℝ) / p := by
  rw [empiricalMeasure_zero_atom, covariance_zero_count_eq_nullity]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg p)),
    div_eq_mul_inv, mul_comm]

/-- Rectangularity forces a zero atom of at least `(p - n) / p`. -/
theorem empiricalMeasure_zero_atom_lower {p n : ℕ} (hp : 0 < p)
    (X : Matrix (Fin p) (Fin n) ℝ) :
    ((p - n : ℕ) : ℝ) / p ≤ (empiricalMeasure X {0}).toReal := by
  rw [empiricalMeasure_zero_atom_real]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (covariance_nullity_ge X))
    (Nat.cast_pos.mpr hp).le

/-- The topological support lies in the nonnegative half-line. -/
theorem empiricalMeasure_support_nonneg {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    (empiricalMeasure X).support ⊆ Set.Ici 0 :=
  Measure.support_subset_of_isClosed isClosed_Ici (empiricalMeasure_ae_nonneg X)

/-- The forced atom in the conventional real-valued rectangular form. -/
theorem empiricalMeasure_zero_atom_lower_real {p n : ℕ} (hp : 0 < p)
    (X : Matrix (Fin p) (Fin n) ℝ) :
    max (1 - (n : ℝ) / p) 0 ≤ (empiricalMeasure X {0}).toReal := by
  apply max_le
  · by_cases hnp : n ≤ p
    · have h := empiricalMeasure_zero_atom_lower hp X
      rw [Nat.cast_sub hnp, sub_div, div_self (by exact_mod_cast hp.ne')] at h
      exact h
    · have hpn : (p : ℝ) ≤ n := by exact_mod_cast (le_of_not_ge hnp)
      have hratio : (1 : ℝ) ≤ (n : ℝ) / p :=
        (le_div_iff₀ (Nat.cast_pos.mpr hp)).mpr (by simpa using hpn)
      exact le_trans (by linarith) ENNReal.toReal_nonneg
  · exact ENNReal.toReal_nonneg

/-- With positive dimensions this is `max (1 - 1 / gamma) 0`, where `gamma = p/n`. -/
theorem empiricalMeasure_zero_atom_aspect_lower {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (X : Matrix (Fin p) (Fin n) ℝ) :
    max (1 - 1 / ((p : ℝ) / n)) 0 ≤ (empiricalMeasure X {0}).toReal := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simpa [div_div, hn0] using empiricalMeasure_zero_atom_lower_real hp X

end RandomMatrix
