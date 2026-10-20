import RandomMatrix.Geometry
import Mathlib.Analysis.Matrix.PosDef

/-! Covariance eigenvalues, their trace moments, and their zero multiplicity. -/

namespace RandomMatrix

/-- The real covariance eigenvalues, indexed with their full multiplicities. -/
noncomputable def covarianceEigenvalues {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    Fin p → ℝ :=
  (covariance_posSemidef X).isHermitian.eigenvalues

theorem covariance_eigenvalues_nonneg {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (i : Fin p) : 0 ≤ covarianceEigenvalues X i :=
  (covariance_posSemidef X).eigenvalues_nonneg i

/-- The same eigenvalue list works for every power, including power zero. -/
theorem covariance_trace_pow {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) (k : ℕ) :
    Matrix.trace (covariance X ^ k) = ∑ i, covarianceEigenvalues X i ^ k := by
  classical
  let hA := (covariance_posSemidef X).isHermitian
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  simp [Matrix.diagonal_pow, Matrix.trace_diagonal, covarianceEigenvalues]

/-- Rank counts nonzero eigenvalues, with multiplicity. -/
theorem covariance_rank_eq_nonzero_count {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    (covariance X).rank = Nat.card {i : Fin p // covarianceEigenvalues X i ≠ 0} := by
  classical
  simpa [covarianceEigenvalues, Nat.card_eq_fintype_card] using
    (covariance_posSemidef X).isHermitian.rank_eq_card_non_zero_eigs

/-- The number of zero eigenvalues is exactly the nullity. -/
theorem covariance_zero_count_eq_nullity {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    Nat.card {i : Fin p // covarianceEigenvalues X i = 0} =
      Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (covariance X))) := by
  classical
  have hsplit := Fintype.card_subtype_compl (fun i : Fin p => covarianceEigenvalues X i = 0)
  have hr := covariance_rank_eq_nonzero_count X
  have hdim := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (covariance X))
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  change (covariance X).rank + _ = p at hdim
  simp only [Nat.card_eq_fintype_card] at hr ⊢
  simp only [Fintype.card_fin] at hsplit
  have hle := Fintype.card_subtype_le (fun i : Fin p => covarianceEigenvalues X i = 0)
  simp only [Fintype.card_fin] at hle
  rw [hr, hsplit] at hdim
  omega

/-- Rectangularity forces at least `p - n` zero eigenvalues. -/
theorem covariance_zero_count_ge {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    p - n ≤ Nat.card {i : Fin p // covarianceEigenvalues X i = 0} := by
  rw [covariance_zero_count_eq_nullity]
  exact covariance_nullity_ge X

end RandomMatrix
