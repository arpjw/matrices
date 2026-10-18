import RandomMatrix.Covariance
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Deterministic positivity and rank bounds for sample covariance matrices. -/

namespace RandomMatrix

/-- Every sample covariance matrix is positive semidefinite. -/
theorem covariance_posSemidef {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    (covariance X).PosSemidef := by
  have h := (Matrix.posSemidef_self_mul_conjTranspose X).smul
    (inv_nonneg.mpr (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  simpa [covariance] using h

/-- Rank is at most the number of samples, even before any randomness assumption. -/
theorem covariance_rank_le {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    (covariance X).rank ≤ n := by
  have h : covariance X = ((n : ℝ)⁻¹ • X) * X.transpose := by
    simp [covariance, Matrix.smul_mul]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- At least p-n null directions are forced when there are more rows than columns. -/
theorem covariance_nullity_ge {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    p - n ≤ Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (covariance X))) := by
  have hr := covariance_rank_le X
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (covariance X))
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  change (covariance X).rank + _ = p at h
  omega

end RandomMatrix
