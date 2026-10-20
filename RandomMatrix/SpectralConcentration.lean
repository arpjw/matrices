import RandomMatrix.EmpiricalMeasure
import RandomMatrix.MomentConcentration

/-! Trace-moment concentration transferred to the actual empirical spectral measures. -/

open MeasureTheory Filter Topology

namespace RandomMatrix

/-- Every sign covariance matrix has empirical first moment one. -/
theorem empiricalMeasure_sign_first_moment {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (ω : Fin p × Fin n → Bool) :
    ∫ x, x ∂empiricalMeasure (signMatrix ω) = 1 := by
  simpa only [pow_one] using (empiricalMeasure_moment (signMatrix ω) 1).trans
    (sign_first_moment hp hn ω)

/-- Expected empirical moments tend to the Narayana moment polynomial. -/
theorem empirical_moment_expected_tendsto (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => average (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ∫ x, x ^ k ∂empiricalMeasure (signMatrix ω))) atTop (nhds (mpMoment k γ)) := by
  simpa only [empiricalMeasure_moment] using
    expected_moment_tendsto p n hp hn hn_top k γ hγ hratio

/-- Quantitative deviations of actual empirical moments at the current aspect ratio. -/
theorem empirical_moment_deviation_bound {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (k : ℕ) (a B ε : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (hε : 0 < ε)
    (hlower : a ≤ (p : ℝ) / n) (hupper : (p : ℝ) / n ≤ B) :
    finiteProbability (fun ω : Fin p × Fin n → Bool =>
      ε < |(∫ x, x ^ k ∂empiricalMeasure (signMatrix ω)) - mpMoment k ((p : ℝ) / n)|) ≤
      (varianceErrorConstant k a B / n + (momentErrorConstant k a B / n) ^ 2) / ε ^ 2 := by
  simpa only [empiricalMeasure_moment] using
    moment_deviation_bound hp hn k a B ε ha hB hε hlower hupper

/-- Mean-square convergence of every fixed empirical spectral moment. -/
theorem empirical_moment_mean_square_tendsto (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => average (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ((∫ x, x ^ k ∂empiricalMeasure (signMatrix ω)) - mpMoment k γ) ^ 2))
      atTop (nhds 0) := by
  simpa only [empiricalMeasure_moment] using
    moment_mean_square_tendsto p n hp hn hn_top k γ hγ hratio

/-- Every fixed moment of the empirical eigenvalue probability measure converges in probability.
This is moment convergence, not yet weak convergence against all bounded continuous functions. -/
theorem empirical_moment_converges_in_probability (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => finiteProbability (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ε < |(∫ x, x ^ k ∂empiricalProbabilityMeasure (hp m) (signMatrix ω)) - mpMoment k γ|))
      atTop (nhds 0) := by
  simpa only [empiricalProbabilityMeasure_coe, empiricalMeasure_moment] using
    moment_converges_in_probability p n hp hn hn_top k γ hγ hratio ε hε

end RandomMatrix
