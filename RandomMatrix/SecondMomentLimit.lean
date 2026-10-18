import RandomMatrix.Covariance
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact finite bias and convergence of the expected second trace moment. -/

open Filter Topology
namespace RandomMatrix

/-- The finite-size bias relative to 1+p/n is exactly -1/n. -/
theorem second_moment_bias {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) 2) -
      (1 + (p : ℝ) / n) = -(1 / (n : ℝ)) := by
  rw [expected_second_moment hp hn]
  ring

/-- Expected second moments converge at every positive-dimensional aspect-ratio limit.
This is an expectation theorem, not convergence of the empirical spectral measures. -/
theorem expected_second_moment_tendsto (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (γ : ℝ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => average (fun ω : Fin (p m) × Fin (n m) → Bool =>
      normalizedMoment (signMatrix ω) 2)) atTop (nhds (1 + γ)) := by
  have hi : Tendsto (fun m => 1 / (n m : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hn_top
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hratio).sub hi
  simp only [sub_zero] at h
  apply h.congr
  intro m
  have hb := second_moment_bias (hp m) (hn m)
  linarith

end RandomMatrix
