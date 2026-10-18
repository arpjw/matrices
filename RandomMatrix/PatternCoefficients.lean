import RandomMatrix.WalkPatterns

/-! Dimension-independent coefficients in the exact falling-factorial moment expansion. -/

open scoped BigOperators Classical
namespace RandomMatrix

theorem blockCount_le {m : ℕ} (s : Setoid (Fin m)) : blockCount s ≤ m := by
  unfold blockCount
  rw [Nat.card_eq_fintype_card]
  simpa using Fintype.card_quotient_le s

noncomputable def rowBlockIndex {k : ℕ} (r : Setoid (Fin (k + 1))) : Fin (k + 2) :=
  ⟨blockCount r, Nat.lt_succ_of_le (blockCount_le r)⟩

noncomputable def colBlockIndex {k : ℕ} (c : Setoid (Fin k)) : Fin (k + 1) :=
  ⟨blockCount c, Nat.lt_succ_of_le (blockCount_le c)⟩

/-- Number of surviving equality patterns with exactly r row blocks and c column blocks. -/
noncomputable def patternCoefficient (k r c : ℕ) : ℕ :=
  Nat.card {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
    PatternSurvives k q.1 q.2 ∧ blockCount q.1 = r ∧ blockCount q.2 = c}

/-- Regrouping partitions by block counts produces the dimension-independent coefficients. -/
theorem evenClosedWalkCount_by_coefficients (p n k : ℕ) :
    evenClosedWalkCount p n k =
      ∑ r : Fin (k + 2), ∑ c : Fin (k + 1),
        patternCoefficient k r c * p.descFactorial r * n.descFactorial c := by
  rw [evenClosedWalkCount_by_patterns]
  have h := sum_by_statistic
    (fun q : Setoid (Fin (k + 1)) × Setoid (Fin k) => PatternSurvives k q.1 q.2)
    (fun q => (rowBlockIndex q.1, colBlockIndex q.2))
    (fun rc : Fin (k + 2) × Fin (k + 1) => p.descFactorial rc.1 * n.descFactorial rc.2)
  have hc (rc : Fin (k + 2) × Fin (k + 1)) :
      Nat.card {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
        PatternSurvives k q.1 q.2 ∧ (rowBlockIndex q.1, colBlockIndex q.2) = rc} =
      patternCoefficient k rc.1 rc.2 := by
    unfold patternCoefficient
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro q
    simp [Prod.ext_iff, Fin.ext_iff, rowBlockIndex, colBlockIndex]
  simp_rw [hc] at h
  simpa only [Fintype.sum_prod_type, rowBlockIndex, colBlockIndex, Nat.mul_assoc] using h

/-- Exact all-order finite moments as a polynomial in falling factorials. -/
theorem expected_moment_by_coefficients {p n : ℕ} (hp : 0 < p) (hn : 0 < n) (k : ℕ) :
    average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) =
      ((∑ r : Fin (k + 2), ∑ c : Fin (k + 1),
        patternCoefficient k r c * p.descFactorial r * n.descFactorial c : ℕ) : ℝ) /
        ((p : ℝ) * (n : ℝ) ^ k) := by
  rw [expected_moment_eq_walk_count hp hn, evenClosedWalkCount_by_coefficients]

end RandomMatrix
