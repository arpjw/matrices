import RandomMatrix.ExpectedMomentBounds

/-! Convergence of every fixed expected trace moment for the actual finite sign ensemble. -/

open Filter Topology
open scoped BigOperators
namespace RandomMatrix

/-- The limiting moment polynomial is continuous in the aspect ratio. -/
theorem continuous_mpMoment (k : ℕ) : Continuous (mpMoment k) := by
  unfold mpMoment
  split_ifs <;> fun_prop

/-- The finite-size bias vanishes when the dimensions diverge at a positive finite ratio. -/
theorem expected_moment_bias_tendsto (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => average (fun ω : Fin (p m) × Fin (n m) → Bool =>
      normalizedMoment (signMatrix ω) k) - mpMoment k ((p m : ℝ) / n m)) atTop (nhds 0) := by
  let a := γ / 2
  let B := max 1 (γ + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 1 ≤ B := le_max_left _ _
  have hlower : ∀ᶠ m in atTop, a ≤ (p m : ℝ) / n m :=
    (hratio.eventually_const_lt (show a < γ by dsimp [a]; linarith)).mono (fun m h => h.le)
  have hupper : ∀ᶠ m in atTop, (p m : ℝ) / n m ≤ B :=
    (hratio.eventually_lt_const (show γ < B by
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _))).mono (fun m h => h.le)
  have hi : Tendsto (fun m => 1 / (n m : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hn_top
  have hbound : Tendsto (fun m => momentErrorConstant k a B / (n m : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, mul_one_div] using hi.const_mul (momentErrorConstant k a B)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hbound
  filter_upwards [hlower, hupper] with m hl hu
  exact expected_moment_error_bound (hp m) (hn m) k a B ha hB hl hu

/-- Every fixed expected normalized trace moment converges to its MP polynomial value.
This theorem does not assert concentration or convergence of the empirical spectral measures. -/
theorem expected_moment_tendsto (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => average (fun ω : Fin (p m) × Fin (n m) → Bool =>
      normalizedMoment (signMatrix ω) k)) atTop (nhds (mpMoment k γ)) := by
  have hb := expected_moment_bias_tendsto p n hp hn hn_top k γ hγ hratio
  have hm := ((continuous_mpMoment k).tendsto γ).comp hratio
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hb.add hm

end RandomMatrix
