import RandomMatrix.MPPolynomialRecurrence
import RandomMatrix.MPParameters

/-! Angular MP moments satisfy the same recurrence as the Narayana polynomials. -/

open MeasureTheory (volume)
open Real intervalIntegral
open scoped BigOperators

namespace RandomMatrix

/-- The angular integral for the positive moment of order `k + 1`. -/
noncomputable def mpAngularMoment (k : ℕ) (γ : ℝ) : ℝ :=
  2 / Real.pi * ∫ t in 0..Real.pi, mpAngle γ t ^ k * Real.sin t ^ 2

theorem mpAngular_integrable (k : ℕ) (γ : ℝ) :
    IntervalIntegrable (fun t => mpAngle γ t ^ k * Real.sin t ^ 2) volume 0 Real.pi :=
  ((mpAngle_continuous γ).pow k |>.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _

@[simp] theorem mpAngularMoment_zero (γ : ℝ) : mpAngularMoment 0 γ = 1 := by
  simp [mpAngularMoment, integral_sin_sq, Real.pi_ne_zero]

theorem mpAngularMoment_one (γ : ℝ) : mpAngularMoment 1 γ = 1 + γ := by
  have he : (fun t => mpAngle γ t ^ 1 * Real.sin t ^ 2) =
      (fun t => (1 + γ) * Real.sin t ^ 2 -
        2 * Real.sqrt γ * (Real.sin t ^ 2 * Real.cos t)) := by
    funext t
    simp [mpAngle]
    ring
  rw [mpAngularMoment, he, integral_sub]
  · simp [integral_const_mul, integral_sin_sq, integral_sin_sq_mul_cos]
    field_simp
  · exact (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.mul ((Real.continuous_sin.pow 2).mul Real.continuous_cos)).intervalIntegrable _ _

/-- Integration by parts yields the three-term recurrence for all positive indices. -/
theorem mpAngularMoment_recurrence (k : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (k + 4 : ℝ) * mpAngularMoment (k + 2) γ =
      (2 * k + 5 : ℝ) * (1 + γ) * mpAngularMoment (k + 1) γ -
        (k + 1 : ℝ) * (γ - 1) ^ 2 * mpAngularMoment k γ := by
  let F := fun t => 2 * Real.sqrt γ * mpAngle γ t ^ (k + 1) * Real.sin t ^ 3
  let D := fun t => -(k + 4 : ℝ) * (mpAngle γ t ^ (k + 2) * Real.sin t ^ 2) +
      (2 * k + 5 : ℝ) * (1 + γ) * (mpAngle γ t ^ (k + 1) * Real.sin t ^ 2) -
      (k + 1 : ℝ) * (γ - 1) ^ 2 * (mpAngle γ t ^ k * Real.sin t ^ 2)
  have hD (t : ℝ) : HasDerivAt F (D t) t := by
    have h := (((mpAngle_hasDerivAt γ t).pow (k + 1)).const_mul
      (2 * Real.sqrt γ)).mul ((Real.hasDerivAt_sin t).pow 3)
    convert h using 1
    dsimp [D, mpAngle]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    linear_combination
      (-(k + 1 : ℝ) * (1 + γ - 2 * Real.sqrt γ * Real.cos t) ^ k *
        Real.sin t ^ 2) * (4 * Real.sqrt γ ^ 2 * (Real.sin_sq_add_cos_sq t)) +
      (-4 * (k + 1 : ℝ) * (1 + γ - 2 * Real.sqrt γ * Real.cos t) ^ k *
        Real.sin t ^ 2) * (Real.sq_sqrt hγ)
  have hi : IntervalIntegrable D volume 0 Real.pi := by
    dsimp [D]
    exact (((mpAngular_integrable (k + 2) γ).const_mul _).add
      ((mpAngular_integrable (k + 1) γ).const_mul _)).sub
      ((mpAngular_integrable k γ).const_mul _)
  have hzero := integral_eq_sub_of_hasDerivAt (fun t _ => hD t) hi
  have hF0 : F 0 = 0 := by simp [F]
  have hFπ : F Real.pi = 0 := by simp [F]
  rw [hF0, hFπ, sub_self] at hzero
  dsimp [D] at hzero
  rw [integral_sub, integral_add] at hzero
  · simp only [integral_const_mul] at hzero
    dsimp [mpAngularMoment]
    linear_combination -(2 / Real.pi) * hzero
  · exact (mpAngular_integrable (k + 2) γ).const_mul _
  · exact (mpAngular_integrable (k + 1) γ).const_mul _
  · exact ((mpAngular_integrable (k + 2) γ).const_mul _).add
      ((mpAngular_integrable (k + 1) γ).const_mul _)
  · exact (mpAngular_integrable k γ).const_mul _

/-- The angular integral is the already formalized Narayana moment at every order. -/
theorem mpAngularMoment_eq_mpMoment (k : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    mpAngularMoment k γ = mpMoment (k + 1) γ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | k
    · simp
    · simpa using mpAngularMoment_one γ
    · have h := mpAngularMoment_recurrence k hγ.le
      rw [ih (k + 1) (by omega), ih k (by omega)] at h
      apply mul_left_cancel₀ (show (k + 4 : ℝ) ≠ 0 by positivity)
      exact h.trans (mpMoment_recurrence k γ hγ.ne').symm

end RandomMatrix
