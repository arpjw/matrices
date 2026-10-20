import RandomMatrix.LabelWeightBounds
import RandomMatrix.MomentPolynomials
import RandomMatrix.PatternBudget

/-! Explicit all-order finite-size bounds for the expected normalized trace moments. -/

open scoped BigOperators Classical
namespace RandomMatrix

/-- The exact finite expansion with each labeling contribution normalized separately. -/
theorem expected_moment_eq_labelWeight {p n : ℕ} (hp : 0 < p) (hn : 0 < n) (k : ℕ) :
    average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) =
      ∑ r : Fin (k + 2), ∑ c : Fin (k + 1),
        (patternCoefficient k r c : ℝ) * normalizedLabelWeight p n k r c := by
  rw [expected_moment_by_coefficients hp hn]
  simp only [Nat.cast_sum, Nat.cast_mul, div_eq_mul_inv, Finset.sum_mul, normalizedLabelWeight,
    mul_assoc]

/-- Finite-size control before imposing a lower bound on the aspect ratio. -/
theorem expected_moment_error_dimensions {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (k : ℕ) (B : ℝ) (hB : 1 ≤ B) (hratio : (p : ℝ) / n ≤ B) :
    |average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) -
        mpMoment k ((p : ℝ) / n)| ≤
      (patternBudget k : ℝ) * B ^ k *
        (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / (p : ℝ) + 1 / (n : ℝ)) + 1 / (n : ℝ)) := by
  let E : ℝ := B ^ k *
    (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / (p : ℝ) + 1 / (n : ℝ)) + 1 / (n : ℝ))
  have hB0 : 0 ≤ B := by linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hterm (r : Fin (k + 2)) (c : Fin (k + 1)) :
      |(patternCoefficient k r c : ℝ) * normalizedLabelWeight p n k r c -
        (if r.val + c.val = k + 1 then
          (patternCoefficient k r c : ℝ) * ((p : ℝ) / n) ^ (r.val - 1) else 0)| ≤
        (patternCoefficient k r c : ℝ) * E := by
    by_cases hz : patternCoefficient k r c = 0
    · simp [hz]
    have hr : 0 < r.val := by
      by_contra h
      have he : r.val = 0 := by omega
      exact hz (by rw [he, patternCoefficient_zero_rows])
    have hs : r.val + c.val ≤ k + 1 := by
      by_contra h
      exact hz (patternCoefficient_eq_zero_of_large k r c (by omega))
    have ht := mul_le_mul_of_nonneg_left
      (labelWeight_error_bound p n k r c B hp hn hB hratio hr hs)
      (show (0 : ℝ) ≤ patternCoefficient k r c by positivity)
    have he : (patternCoefficient k r c : ℝ) * normalizedLabelWeight p n k r c -
        (if r.val + c.val = k + 1 then
          (patternCoefficient k r c : ℝ) * ((p : ℝ) / n) ^ (r.val - 1) else 0) =
        (patternCoefficient k r c : ℝ) * (normalizedLabelWeight p n k r c -
          (if r.val + c.val = k + 1 then ((p : ℝ) / n) ^ (r.val - 1) else 0)) := by
      split_ifs <;> ring
    rw [he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ patternCoefficient k r c by positivity)]
    exact ht
  rw [← leadingMoment_eq_mpMoment, expected_moment_eq_labelWeight hp hn, leadingMoment,
    ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r : Fin (k + 2), |∑ c : Fin (k + 1),
        ((patternCoefficient k r c : ℝ) * normalizedLabelWeight p n k r c -
          (if r.val + c.val = k + 1 then
            (patternCoefficient k r c : ℝ) * ((p : ℝ) / n) ^ (r.val - 1) else 0))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin (k + 2), ∑ c : Fin (k + 1),
        (patternCoefficient k r c : ℝ) * E := by
      apply Finset.sum_le_sum
      intro r hr
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c hc => hterm r c))
    _ = (∑ r : Fin (k + 2), ∑ c : Fin (k + 1), (patternCoefficient k r c : ℝ)) * E := by
      simp only [Finset.sum_mul]
    _ ≤ (patternBudget k : ℝ) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast sum_patternCoefficient_le_budget k
    _ = _ := by simp only [E, mul_assoc]

/-- An explicit, conservative constant for a compact positive aspect-ratio interval. -/
noncomputable def momentErrorConstant (k : ℕ) (a B : ℝ) : ℝ :=
  (patternBudget k : ℝ) * B ^ k * (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / a + 1) + 1)

/-- Uniform O(1/n) bias relative to the MP polynomial evaluated at the current ratio.
No convergence rate for the ratio itself is assumed. -/
theorem expected_moment_error_bound {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (k : ℕ) (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (hlower : a ≤ (p : ℝ) / n) (hupper : (p : ℝ) / n ≤ B) :
    |average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) -
        mpMoment k ((p : ℝ) / n)| ≤ momentErrorConstant k a B / n := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : 0 ≤ B := by linarith
  have han : a * n ≤ (p : ℝ) := (le_div_iff₀ hnR).mp hlower
  have hinv : 1 / (p : ℝ) ≤ 1 / (a * n) := one_div_le_one_div_of_le (by positivity) han
  apply (expected_moment_error_dimensions hp hn k B hB hupper).trans
  calc
    _ ≤ (patternBudget k : ℝ) * B ^ k *
        (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / (a * n) + 1 / (n : ℝ)) + 1 / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      gcongr
    _ = _ := by unfold momentErrorConstant; field_simp

end RandomMatrix
