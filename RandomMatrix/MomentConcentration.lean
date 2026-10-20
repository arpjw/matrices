import RandomMatrix.VarianceBounds
import RandomMatrix.ExpectedMomentLimit

/-! Quantitative concentration and convergence in probability of every fixed trace moment. -/

open Filter Topology
namespace RandomMatrix

/-- A finite Chebyshev bound around the MP polynomial at the current aspect ratio. -/
theorem moment_deviation_bound {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (k : ℕ) (a B ε : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (hε : 0 < ε)
    (hlower : a ≤ (p : ℝ) / n) (hupper : (p : ℝ) / n ≤ B) :
    finiteProbability (fun ω : Fin p × Fin n → Bool =>
      ε < |normalizedMoment (signMatrix ω) k - mpMoment k ((p : ℝ) / n)|) ≤
      (varianceErrorConstant k a B / n + (momentErrorConstant k a B / n) ^ 2) / ε ^ 2 := by
  have hB0 : 0 ≤ B := by linarith
  have hb := expected_moment_error_bound hp hn k a B ha hB hlower hupper
  have hc : 0 ≤ momentErrorConstant k a B / n := by unfold momentErrorConstant; positivity
  have hs := (sq_le_sq₀ (abs_nonneg _) hc).mpr hb
  rw [sq_abs] at hs
  have hv := moment_variance_bound hp hn k a B ha hB hlower hupper
  apply (finite_chebyshev_center _ _ ε hε).trans
  rw [mean_square_eq_variance_add_bias]
  exact div_le_div_of_nonneg_right (add_le_add hv hs) (sq_nonneg ε)

/-- Variances vanish along every positive finite aspect-ratio limit. -/
theorem moment_variance_tendsto (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => finiteVariance (fun ω : Fin (p m) × Fin (n m) → Bool =>
      normalizedMoment (signMatrix ω) k)) atTop (nhds 0) := by
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
  have hbound : Tendsto (fun m => varianceErrorConstant k a B / (n m : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, mul_one_div] using hi.const_mul (varianceErrorConstant k a B)
  apply squeeze_zero' (Eventually.of_forall (fun _ => finiteVariance_nonneg _)) _ hbound
  filter_upwards [hlower, hupper] with m hl hu
  exact moment_variance_bound (hp m) (hn m) k a B ha hB hl hu

/-- The mean-square error to the limiting moment tends to zero. -/
theorem moment_mean_square_tendsto (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) :
    Tendsto (fun m => average (fun ω : Fin (p m) × Fin (n m) → Bool =>
      (normalizedMoment (signMatrix ω) k - mpMoment k γ) ^ 2)) atTop (nhds 0) := by
  have hv := moment_variance_tendsto p n hp hn hn_top k γ hγ hratio
  have hm := expected_moment_tendsto p n hp hn hn_top k γ hγ hratio
  have hb := (hm.sub_const (mpMoment k γ)).pow 2
  simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hb
  have h := hv.add hb
  simp only [zero_add] at h
  apply h.congr
  intro m
  exact (mean_square_eq_variance_add_bias _ _).symm

/-- Every fixed random trace moment converges in probability to its MP polynomial value.
The probability is the exact uniform fraction in each finite ensemble separately. -/
theorem moment_converges_in_probability (p n : ℕ → ℕ) (hp : ∀ m, 0 < p m)
    (hn : ∀ m, 0 < n m) (hn_top : Tendsto n atTop atTop) (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hratio : Tendsto (fun m => (p m : ℝ) / n m) atTop (nhds γ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => finiteProbability (fun ω : Fin (p m) × Fin (n m) → Bool =>
      ε < |normalizedMoment (signMatrix ω) k - mpMoment k γ|)) atTop (nhds 0) := by
  have hm := moment_mean_square_tendsto p n hp hn hn_top k γ hγ hratio
  have hbound := hm.div_const (ε ^ 2)
  simp only [zero_div] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun _ => finiteProbability_nonneg _)) _ hbound
  exact Eventually.of_forall (fun _ => finite_chebyshev_center _ _ ε hε)

end RandomMatrix
