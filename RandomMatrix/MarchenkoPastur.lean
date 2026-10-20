import RandomMatrix.MPIdentification
import RandomMatrix.CompactMomentMethod
import RandomMatrix.SpectralTightness

/-! The Marchenko-Pastur theorem for independent fair-sign sample covariance matrices. -/

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace RandomMatrix

theorem marchenkoPastur_ae_interval (γ : ℝ) :
    ∀ᵐ x ∂marchenkoPastur γ, x ∈ Icc 0 (mpUpper γ) := by
  rw [ae_iff]
  exact marchenkoPastur_compl_support_interval γ

/-- The MP moments uniquely identify the full density-plus-atom law among nonnegative
probability measures with integrable natural moments. -/
theorem marchenkoPastur_moment_determinate (γ : ℝ) (hγ : 0 < γ) (μ : ProbabilityMeasure ℝ)
    (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ))
    (hpos : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x)
    (hmom : ∀ k : ℕ, (∫ x : ℝ, x ^ k ∂(μ : Measure ℝ)) = mpMoment k γ) :
    μ = mpProbabilityMeasure γ hγ := by
  apply compact_moments_determine μ (mpProbabilityMeasure γ hγ) hint
    (fun k => marchenkoPastur_moment_integrable k hγ) hpos
    (mpUpper γ) (sq_nonneg _) (marchenkoPastur_ae_interval γ)
  intro k
  simpa only [mpProbabilityMeasure_coe, marchenkoPastur_moment k hγ] using hmom k

/-- Marchenko-Pastur weak convergence in probability for the actual finite fair-sign ensemble.
The eigenvalue measure uses all p eigenvalues of XXᵀ/n, including zeros and multiplicities.
The limiting law is the explicitly normalized MP density plus its zero atom, for every gamma>0.
No joint distribution across matrix sizes is required. -/
theorem empirical_weak_converges_to_mp (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ))
    (f : ℝ →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => finiteProbability (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ε < |(∫ x, f x ∂empiricalProbabilityMeasure (hp m) (signMatrix ω)) -
        ∫ x, f x ∂mpProbabilityMeasure γ hγ|)) atTop (nhds 0) := by
  exact compact_moment_method
    (fun m ω => empiricalProbabilityMeasure (hp m) (signMatrix ω))
    (mpProbabilityMeasure γ hγ)
    (fun _ ω k => empiricalMeasure_integrable (signMatrix ω) (fun x => x ^ k))
    (fun k => marchenkoPastur_moment_integrable k hγ)
    (fun _ ω => empiricalMeasure_ae_nonneg (signMatrix ω))
    (mpUpper γ) (sq_nonneg _) (marchenkoPastur_ae_interval γ)
    (fun k δ hδ => empirical_moment_converges_to_mp p n hp hn hn_top k γ hγ hratio δ hδ)
    f ε hε

/-- The flagship theorem stated using an ordinary continuous function and an explicit bound. -/
theorem marchenkoPastur_theorem (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ))
    (f : ℝ → ℝ) (hf : Continuous f) (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => finiteProbability (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ε < |(∫ x, f x ∂empiricalMeasure (signMatrix ω)) -
        ∫ x, f x ∂marchenkoPastur γ|)) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hbounded
  let F : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) (by
    intro x y
    change |f x - f y| ≤ 2 * M
    exact (abs_sub _ _).trans (by linarith [hM x, hM y]))
  exact empirical_weak_converges_to_mp p n hp hn hn_top γ hγ hratio F ε hε

end RandomMatrix
