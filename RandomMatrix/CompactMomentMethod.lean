import RandomMatrix.PolynomialSandwich
import RandomMatrix.PolynomialIntegrals

/-! The moment method for a compactly supported limit on the nonnegative half-line. -/

open MeasureTheory Set Filter Topology
open scoped Polynomial BoundedContinuousFunction

namespace RandomMatrix

/-- Polynomial upper and lower bounds remain bounds after integration. -/
theorem integral_polynomial_sandwich (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ k, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ))
    (hpos : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x) (f : ℝ →ᵇ ℝ) (l u : ℝ[X])
    (hbound : ∀ x, 0 ≤ x → l.eval x ≤ f x ∧ f x ≤ u.eval x) :
    (∫ x, l.eval x ∂μ) ≤ (∫ x, f x ∂μ) ∧ (∫ x, f x ∂μ) ≤ ∫ x, u.eval x ∂μ := by
  constructor
  · exact integral_mono_ae (polynomial_integrable l hμ) (f.integrable _)
      (hpos.mono fun x hx => (hbound x hx).1)
  · exact integral_mono_ae (f.integrable _) (polynomial_integrable u hμ)
      (hpos.mono fun x hx => (hbound x hx).2)

/-- A uniform gap on the support controls the gap of the polynomial integrals. -/
theorem integral_polynomial_gap (ν : ProbabilityMeasure ℝ)
    (hν : ∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ))
    (B : ℝ) (hsupport : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc 0 B)
    (l u : ℝ[X]) (ε : ℝ) (hgap : ∀ x ∈ Icc 0 B, u.eval x - l.eval x ≤ ε) :
    (∫ x, u.eval x ∂ν) - (∫ x, l.eval x ∂ν) ≤ ε := by
  have h := integral_mono_ae ((polynomial_integrable u hν).sub (polynomial_integrable l hν))
    (integrable_const ε) (hsupport.mono fun x hx => hgap x hx)
  simpa only [Pi.sub_apply, integral_sub (polynomial_integrable u hν) (polynomial_integrable l hν),
    integral_const, probReal_univ, one_smul] using h

/-- All moments converging in probability to a compactly supported law imply weak convergence
in probability. Each index has its own finite sample space; no coupling is assumed. -/
theorem compact_moment_method {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]
    (μ : ∀ m, Ω m → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hμ : ∀ m ω k, Integrable (fun x : ℝ => x ^ k) (μ m ω : Measure ℝ))
    (hν : ∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ))
    (hpos : ∀ m ω, ∀ᵐ x ∂(μ m ω : Measure ℝ), 0 ≤ x)
    (B : ℝ) (hB : 0 ≤ B) (hsupport : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc 0 B)
    (hlim : ∀ k, FiniteConvergesInProbability (fun m ω => ∫ x, x ^ k ∂μ m ω)
      (∫ x, x ^ k ∂ν)) (f : ℝ →ᵇ ℝ) :
    FiniteConvergesInProbability (fun m ω => ∫ x, f x ∂μ m ω) (∫ x, f x ∂ν) := by
  intro ε hε
  obtain ⟨l, u, hbound, hgap⟩ := exists_polynomial_sandwich f B hB (ε / 2) (by positivity)
  have hνpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x := hsupport.mono fun _ hx => hx.1
  obtain ⟨hlν, huν⟩ := integral_polynomial_sandwich ν hν hνpos f l u hbound
  have hgapν := integral_polynomial_gap ν hν B hsupport l u (ε / 2) hgap
  have hpoly (p : ℝ[X]) := polynomial_integral_converges
    (fun m ω => (μ m ω : Measure ℝ)) (ν : Measure ℝ) hμ hν hlim p
  have hprob (m : ℕ) :
      finiteProbability (fun ω => ε < |(∫ x, f x ∂μ m ω) - ∫ x, f x ∂ν|) ≤
      finiteProbability (fun ω => ε / 2 < |(∫ x, l.eval x ∂μ m ω) - ∫ x, l.eval x ∂ν|) +
      finiteProbability (fun ω => ε / 2 < |(∫ x, u.eval x ∂μ m ω) - ∫ x, u.eval x ∂ν|) := by
    refine (finiteProbability_mono _ _ fun ω h => ?_).trans (finiteProbability_or_le _ _)
    obtain ⟨hlμ, huμ⟩ := integral_polynomial_sandwich (μ m ω) (hμ m ω) (hpos m ω) f l u hbound
    by_contra hn
    push_neg at hn
    have hl := abs_le.mp hn.1
    have hu := abs_le.mp hn.2
    have hab : |(∫ x, f x ∂μ m ω) - ∫ x, f x ∂ν| ≤ ε :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact not_lt_of_ge hab h
  exact squeeze_zero (fun _ => finiteProbability_nonneg _) hprob
    (by simpa using (hpoly l (ε / 2) (by positivity)).add (hpoly u (ε / 2) (by positivity)))

/-- A compactly supported probability on the nonnegative half-line is determined by all its
natural moments, even among laws whose supports are not assumed bounded. -/
theorem compact_moments_determine (μ ν : ProbabilityMeasure ℝ)
    (hμ : ∀ k, Integrable (fun x : ℝ => x ^ k) (μ : Measure ℝ))
    (hν : ∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ))
    (hpos : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x)
    (B : ℝ) (hB : 0 ≤ B) (hsupport : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc 0 B)
    (hmom : ∀ k : ℕ, (∫ x : ℝ, x ^ k ∂(μ : Measure ℝ)) =
      ∫ x : ℝ, x ^ k ∂(ν : Measure ℝ)) : μ = ν := by
  have hpoly (p : ℝ[X]) : (∫ x, p.eval x ∂μ) = ∫ x, p.eval x ∂ν := by
    simp only [polynomial_integral_eq_sum p hμ, polynomial_integral_eq_sum p hν, hmom]
  have heq (f : ℝ →ᵇ ℝ) : (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
    have hclose (ε : ℝ) (hε : 0 < ε) : |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ ε := by
      obtain ⟨l, u, hbound, hgap⟩ := exists_polynomial_sandwich f B hB ε hε
      obtain ⟨hlμ, huμ⟩ := integral_polynomial_sandwich μ hμ hpos f l u hbound
      obtain ⟨hlν, huν⟩ := integral_polynomial_sandwich ν hν
        (hsupport.mono fun _ hx => hx.1) f l u hbound
      have hgapν := integral_polynomial_gap ν hν B hsupport l u ε hgap
      rw [hpoly l] at hlμ
      rw [hpoly u] at huμ
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hz : |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 0 :=
      le_of_forall_gt fun ε hε => (hclose (ε / 2) (by positivity)).trans_lt (by linarith)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))
  have hfinite : μ.toFiniteMeasure = ν.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq heq
  exact ProbabilityMeasure.toMeasure_injective (congrArg (fun η : FiniteMeasure ℝ =>
    (η : Measure ℝ)) hfinite)

end RandomMatrix
