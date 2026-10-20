import RandomMatrix.FiniteVariance
import RandomMatrix.PairCounting

/-! Expand the actual trace-moment variance and retain only overlapping even pairs. -/

open scoped BigOperators Classical
namespace RandomMatrix

noncomputable def closedWalkMonomial {p n k : ℕ} (w : Fin p × WalkSteps p n k)
    (ω : Fin p × Fin n → Bool) : ℝ :=
  if walkEnd w.1 w.2 = w.1 then
    ((walkWord w.1 w.2).map (fun e => sign (ω e))).prod else 0

theorem normalizedMoment_eq_walkSum {p n : ℕ} (ω : Fin p × Fin n → Bool) (k : ℕ) :
    normalizedMoment (signMatrix ω) k = ((p : ℝ) * (n : ℝ) ^ k)⁻¹ *
      ∑ w : Fin p × WalkSteps p n k, closedWalkMonomial w ω := by
  simp only [normalizedMoment, trace_covariance_pow_walks, Fintype.sum_prod_type,
    closedWalkMonomial, signMatrix, mul_inv, inv_pow]
  ring

/-- A shared matrix entry supplies the shared row in the joint-partition bound. -/
theorem word_overlap_pair_survives {p n k : ℕ}
    (u v : Fin p × WalkSteps p n k)
    (hj : ∀ e, Even ((walkWord u.1 u.2).count e + (walkWord v.1 v.2).count e))
    (ho : ∃ e, e ∈ walkWord u.1 u.2 ∧ e ∈ walkWord v.1 v.2) :
    PairPatternSurvives k (Setoid.ker (pairWalkLabelsEquiv p n k (u, v)).1)
      (Setoid.ker (pairWalkLabelsEquiv p n k (u, v)).2) := by
  rw [pair_survives_kernel_iff, pairPositionWord_map_labels]
  constructor
  · obtain ⟨e, heu, hev⟩ := ho
    have hu : e.1 ∈ Set.range (walkRowLabels u.1 u.2) := by
      rw [walkRowLabels_range]
      exact (walkWord_mem_vertices u.1 u.2 e heu).1
    have hv : e.1 ∈ Set.range (walkRowLabels v.1 v.2) := by
      rw [walkRowLabels_range]
      exact (walkWord_mem_vertices v.1 v.2 e hev).1
    obtain ⟨i, hi⟩ := hu
    obtain ⟨j, hj⟩ := hv
    exact ⟨i, j, hi.trans hj.symm⟩
  · simpa only [List.count_append] using hj

/-- Every covariance term is bounded by its joint-pattern indicator. -/
theorem closedWalk_covariance_le_pair {p n k : ℕ} (u v : Fin p × WalkSteps p n k) :
    finiteCovariance (closedWalkMonomial u) (closedWalkMonomial v) ≤
      if PairPatternSurvives k (Setoid.ker (pairWalkLabelsEquiv p n k (u, v)).1)
        (Setoid.ker (pairWalkLabelsEquiv p n k (u, v)).2) then 1 else 0 := by
  change finiteCovariance
    (fun ω : Fin p × Fin n → Bool => if walkEnd u.1 u.2 = u.1 then
      ((walkWord u.1 u.2).map (fun e => sign (ω e))).prod else 0)
    (fun ω : Fin p × Fin n → Bool => if walkEnd v.1 v.2 = v.1 then
      ((walkWord v.1 v.2).map (fun e => sign (ω e))).prod else 0) ≤ _
  by_cases hu : walkEnd u.1 u.2 = u.1
  · by_cases hv : walkEnd v.1 v.2 = v.1
    · simp only [hu, hv, ↓reduceIte]
      apply (word_covariance_le_overlap (walkWord u.1 u.2) (walkWord v.1 v.2)).trans
      by_cases h : (∀ e, Even ((walkWord u.1 u.2).count e + (walkWord v.1 v.2).count e)) ∧
          (∃ e, e ∈ walkWord u.1 u.2 ∧ e ∈ walkWord v.1 v.2)
      · rw [if_pos h, if_pos (word_overlap_pair_survives u v h.1 h.2)]
      · rw [if_neg h]
        split_ifs <;> norm_num
    · simp only [hv, ↓reduceIte, finiteCovariance, mul_zero,
        average_const, sub_zero]
      split_ifs <;> norm_num
  · simp only [hu, ↓reduceIte, finiteCovariance, zero_mul,
      average_const, sub_zero]
    split_ifs <;> norm_num

/-- Exact covariance expansion of the normalized trace-moment variance. -/
theorem variance_eq_walk_covariance (p n k : ℕ) :
    finiteVariance (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) =
      ((p : ℝ) * (n : ℝ) ^ k)⁻¹ * ((p : ℝ) * (n : ℝ) ^ k)⁻¹ *
        ∑ u : Fin p × WalkSteps p n k, ∑ v : Fin p × WalkSteps p n k,
          finiteCovariance (closedWalkMonomial u) (closedWalkMonomial v) := by
  rw [finiteVariance_eq_covariance]
  simp_rw [normalizedMoment_eq_walkSum]
  rw [finiteCovariance_mul, finiteCovariance_sum]

/-- The variance is bounded by a concrete finite count, with the full normalization retained. -/
theorem variance_le_pairWalkCount {p n : ℕ} (hp : 0 < p) (hn : 0 < n) (k : ℕ) :
    finiteVariance (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) ≤
      (pairWalkCount p n k : ℝ) / ((p : ℝ) ^ 2 * (n : ℝ) ^ (2 * k)) := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsum : (∑ u : Fin p × WalkSteps p n k, ∑ v : Fin p × WalkSteps p n k,
      finiteCovariance (closedWalkMonomial u) (closedWalkMonomial v)) ≤
      (pairWalkCount p n k : ℝ) := by
    calc
      _ ≤ ∑ u : Fin p × WalkSteps p n k, ∑ v : Fin p × WalkSteps p n k,
          if PairPatternSurvives k (Setoid.ker (pairWalkLabelsEquiv p n k (u, v)).1)
            (Setoid.ker (pairWalkLabelsEquiv p n k (u, v)).2) then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro u hu
        exact Finset.sum_le_sum (fun v hv => closedWalk_covariance_le_pair u v)
      _ = _ := by
        simp only [pairWalkCount, Fintype.sum_prod_type, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero]
  rw [variance_eq_walk_covariance]
  calc
    _ ≤ ((p : ℝ) * (n : ℝ) ^ k)⁻¹ * ((p : ℝ) * (n : ℝ) ^ k)⁻¹ *
        (pairWalkCount p n k : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [show 2 * k = k * 2 by omega, pow_mul]
      field_simp

end RandomMatrix
