import RandomMatrix.Rademacher
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Real sample covariance matrices with the convention S = X Xᵀ / n. -/

open scoped BigOperators
namespace RandomMatrix

noncomputable def covariance {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := (n : ℝ)⁻¹ • (X * X.transpose)

def signMatrix {p n : ℕ} (ω : Fin p × Fin n → Bool) : Matrix (Fin p) (Fin n) ℝ :=
  fun i a => sign (ω (i, a))

noncomputable def normalizedMoment {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (k : ℕ) : ℝ := (p : ℝ)⁻¹ * Matrix.trace (covariance X ^ k)

@[simp] theorem covariance_apply {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (i j : Fin p) :
    covariance X i j = (n : ℝ)⁻¹ * ∑ a, X i a * X j a := by
  simp [covariance, Matrix.mul_apply]

theorem covariance_symmetric {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (i j : Fin p) : covariance X i j = covariance X j i := by
  simp [mul_comm]

@[simp] theorem sign_covariance_diagonal {p n : ℕ} (hn : 0 < n)
    (ω : Fin p × Fin n → Bool) (i : Fin p) : covariance (signMatrix ω) i i = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [covariance_apply, signMatrix, ← pow_two, hn']

/-- The first normalized moment is exactly one for every sign matrix. -/
theorem sign_first_moment {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (ω : Fin p × Fin n → Bool) : normalizedMoment (signMatrix ω) 1 = 1 := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [normalizedMoment, pow_one, Matrix.trace, Matrix.diag_apply,
    sign_covariance_diagonal hn]
  simp [hp']

/-- An exact finite-dimensional trace expansion, before taking expectations. -/
theorem trace_covariance_sq {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ) :
    Matrix.trace (covariance X ^ 2) =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ∑ a, ∑ b,
        X i a * X j a * X j b * X i b := by
  simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    covariance_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Count the surviving rectangles in a p-by-n sign matrix. -/
theorem rectangle_count (p n : ℕ) :
    (∑ i : Fin p, ∑ j : Fin p, ∑ a : Fin n, ∑ b : Fin n,
      if i = j ∨ a = b then (1 : ℝ) else 0) =
      p * n ^ 2 + p * (p - 1 : ℝ) * n := by
  have hinner (i j : Fin p) :
      (∑ a : Fin n, ∑ b : Fin n, if i = j ∨ a = b then (1 : ℝ) else 0) =
      if i = j then (n : ℝ) ^ 2 else n := by
    by_cases h : i = j <;> simp [h, sq]
  simp_rw [hinner]
  have hrow (i : Fin p) :
      (∑ j : Fin p, if i = j then (n : ℝ) ^ 2 else n) =
        (n : ℝ) ^ 2 + (p - 1 : ℝ) * n := by
    have heq (j : Fin p) : (if i = j then (n : ℝ) ^ 2 else n) =
        (if i = j then (n : ℝ) ^ 2 - n else 0) + n := by
      split_ifs <;> ring
    simp_rw [heq]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hrow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The exact second moment for iid fair signs, with both finite-size corrections visible. -/
theorem expected_second_moment {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) 2) =
      1 + (p - 1 : ℝ) / n := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [normalizedMoment, trace_covariance_sq, signMatrix]
  rw [average_mul_const, average_mul_const]
  simp_rw [average_sum, average_rectangle]
  rw [rectangle_count]
  field_simp

end RandomMatrix
