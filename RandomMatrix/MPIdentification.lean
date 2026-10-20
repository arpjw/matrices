import RandomMatrix.MPMeasure
import RandomMatrix.SpectralConcentration

/-! Empirical moment limits identified with the explicit MP probability measure. -/

open MeasureTheory Filter Topology

namespace RandomMatrix

/-- The mean-square empirical moment limit is the moment of the explicit density-plus-atom law. -/
theorem empirical_moment_mean_square_to_mp (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => average (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ((∫ x, x ^ k ∂empiricalMeasure (signMatrix ω)) -
        ∫ x, x ^ k ∂marchenkoPastur γ) ^ 2)) atTop (nhds 0) := by
  simpa only [marchenkoPastur_moment k hγ] using
    empirical_moment_mean_square_tendsto p n hp hn hn_top k γ hγ hratio

/-- Every fixed empirical moment converges in probability to the corresponding moment of the
explicit MP probability measure. Weak convergence for bounded continuous tests is a later step. -/
theorem empirical_moment_converges_to_mp (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => finiteProbability (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ε < |(∫ x, x ^ k ∂empiricalProbabilityMeasure (hp m) (signMatrix ω)) -
        ∫ x, x ^ k ∂mpProbabilityMeasure γ hγ|)) atTop (nhds 0) := by
  simpa only [mpProbabilityMeasure_coe, marchenkoPastur_moment k hγ] using
    empirical_moment_converges_in_probability p n hp hn hn_top k γ hγ hratio ε hε

end RandomMatrix
