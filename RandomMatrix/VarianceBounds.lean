import RandomMatrix.WalkCovariance
import RandomMatrix.PairCountBounds

/-! Explicit variance bounds for every fixed normalized trace moment. -/

namespace RandomMatrix

/-- One inverse row dimension remains after counting connected even walk pairs. -/
theorem moment_variance_le_rows {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (k : ℕ) (B : ℝ) (hB : 1 ≤ B) (hratio : (p : ℝ) / n ≤ B) :
    finiteVariance (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) ≤
      (pairPatternBudget k : ℝ) * B ^ (2 * k) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (variance_le_pairWalkCount hp hn k).trans
  calc
    _ = ((pairWalkCount p n k : ℝ) / ((p : ℝ) * (n : ℝ) ^ (2 * k))) / p := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (pairWalkCount_normalized_le hp hn k B hB hratio) hpR.le

noncomputable def varianceErrorConstant (k : ℕ) (a B : ℝ) : ℝ :=
  (pairPatternBudget k : ℝ) * B ^ (2 * k) / a

/-- A uniform O(1/n) variance bound on every compact positive aspect-ratio interval. -/
theorem moment_variance_bound {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (k : ℕ) (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (hlower : a ≤ (p : ℝ) / n) (hupper : (p : ℝ) / n ≤ B) :
    finiteVariance (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) ≤
      varianceErrorConstant k a B / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : 0 ≤ B := by linarith
  have han : a * n ≤ (p : ℝ) := (le_div_iff₀ hnR).mp hlower
  apply (moment_variance_le_rows hp hn k B hB hupper).trans
  calc
    _ ≤ (pairPatternBudget k : ℝ) * B ^ (2 * k) / (a * n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) han
    _ = _ := by unfold varianceErrorConstant; ring

end RandomMatrix
