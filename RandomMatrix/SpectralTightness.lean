import RandomMatrix.SpectralConcentration
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Deterministic uniform tightness from the exact first spectral moment. -/

open MeasureTheory Set

namespace RandomMatrix

/-- Every fair-sign covariance spectrum has at most `1/R` mass outside `[0,R]`. -/
theorem empirical_sign_tail_bound {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (ω : Fin p × Fin n → Bool) (R : ℝ) (hR : 0 < R) :
    empiricalMeasure (signMatrix ω) (Icc 0 R)ᶜ ≤ ENNReal.ofReal (1 / R) := by
  have ht : empiricalMeasure (signMatrix ω) (Ioi R) ≤ ENNReal.ofReal (1 / R) := by
    have h := (empiricalMeasure_integrable (signMatrix ω) (fun x => x / R)).measure_le_integral
      ((empiricalMeasure_ae_nonneg (signMatrix ω)).mono fun x hx => div_nonneg hx hR.le)
      (s := Ioi R) (fun x hx => (one_le_div hR).mpr hx.le)
    simpa only [integral_div, empiricalMeasure_sign_first_moment hp hn ω] using h
  calc
    _ = empiricalMeasure (signMatrix ω) (Iio 0 ∪ Ioi R) := by
      congr 1
      ext x
      simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
    _ ≤ empiricalMeasure (signMatrix ω) (Iio 0) + empiricalMeasure (signMatrix ω) (Ioi R) :=
      measure_union_le _ _
    _ = empiricalMeasure (signMatrix ω) (Ioi R) := by
      rw [empiricalMeasure_negative, zero_add]
    _ ≤ _ := ht

/-- A single compact interval works for all positive dimensions and all sign matrices. -/
theorem empirical_sign_uniform_tightness (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set ℝ, IsCompact K ∧ ∀ (p n : ℕ) (_hp : 0 < p) (_hn : 0 < n)
      (ω : Fin p × Fin n → Bool), empiricalMeasure (signMatrix ω) Kᶜ ≤ ENNReal.ofReal ε := by
  refine ⟨Icc 0 (1 / ε), isCompact_Icc, ?_⟩
  intro p n hp hn ω
  simpa only [one_div_one_div] using empirical_sign_tail_bound hp hn ω (1 / ε) (by positivity)

end RandomMatrix
