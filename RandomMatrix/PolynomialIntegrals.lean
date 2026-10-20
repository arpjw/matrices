import RandomMatrix.FiniteConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Polynomial integrals and their convergence from the individual natural moments. -/

open MeasureTheory Filter Topology
open scoped BigOperators Polynomial

namespace RandomMatrix

/-- All natural moments being integrable implies integrability of every polynomial. -/
theorem polynomial_integrable (p : ℝ[X]) {μ : Measure ℝ}
    (hμ : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) : Integrable p.eval μ := by
  simp_rw [Polynomial.eval_eq_sum_range]
  exact integrable_finset_sum _ (fun i _ => (hμ i).const_mul (p.coeff i))

/-- Integration of a polynomial is the finite linear combination of its moments. -/
theorem polynomial_integral_eq_sum (p : ℝ[X]) {μ : Measure ℝ}
    (hμ : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) :
    (∫ x, p.eval x ∂μ) =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∫ x, x ^ i ∂μ := by
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finset_sum _ (fun i _ => (hμ i).const_mul (p.coeff i))]
  simp only [integral_const_mul]

/-- Convergence of every moment in probability gives convergence of every polynomial integral. -/
theorem polynomial_integral_converges {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]
    (μ : ∀ m, Ω m → Measure ℝ) (ν : Measure ℝ)
    (hμ : ∀ m ω k, Integrable (fun x : ℝ => x ^ k) (μ m ω))
    (hν : ∀ k, Integrable (fun x : ℝ => x ^ k) ν)
    (hlim : ∀ k, FiniteConvergesInProbability (fun m ω => ∫ x, x ^ k ∂μ m ω)
      (∫ x, x ^ k ∂ν)) (p : ℝ[X]) :
    FiniteConvergesInProbability (fun m ω => ∫ x, p.eval x ∂μ m ω) (∫ x, p.eval x ∂ν) := by
  simp_rw [polynomial_integral_eq_sum p (hμ _ _), polynomial_integral_eq_sum p hν]
  exact finiteConverges_sum _ _ _ (fun i _ => (hlim i).const_mul (p.coeff i))

end RandomMatrix
