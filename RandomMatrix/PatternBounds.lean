import RandomMatrix.PatternCoefficients

/-! The all-order vertex bound transferred from concrete walks to partition coefficients. -/

open scoped Classical
namespace RandomMatrix

/-- Choose one representative label for each block, within the original position type. -/
noncomputable def representativeLabeling {α : Type*} (r : Setoid α) :
    {f : α → α // Setoid.ker f = r} :=
  (kernelFiberEquiv r).symm ⟨Quotient.out, Quotient.out_injective⟩

theorem row_blocks_eq_visited_rows {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    blockCount (Setoid.ker (walkRowLabels i s)) = (walkRows i s).card := by
  unfold blockCount
  rw [Nat.card_congr (Setoid.quotientKerEquivRange (walkRowLabels i s)), walkRowLabels_range]
  simp [Nat.card_eq_fintype_card]

theorem col_blocks_eq_visited_cols {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    blockCount (Setoid.ker (walkColLabels s)) = (walkCols i s).card := by
  unfold blockCount
  rw [Nat.card_congr (Setoid.quotientKerEquivRange (walkColLabels s)), walkColLabels_range i]
  simp [Nat.card_eq_fintype_card]

/-- Every surviving abstract pattern obeys the same vertex bound as a concrete walk. -/
theorem surviving_pattern_block_bound {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    blockCount r + blockCount c ≤ k + 1 := by
  let f := representativeLabeling r
  let g := representativeLabeling c
  let s := stepsFromLabels f.1 g.1
  have hr : walkRowLabels (f.1 0) s = f.1 := rowsFromLabels_inverse _ _
  have hc : walkColLabels s = g.1 := colsFromLabels_inverse _ _
  have hw : IsEvenClosedWalk (f.1 0, s) := by
    rw [isEvenClosedWalk_iff_pattern, hr, hc, f.2, g.2]
    exact h
  have hb := even_walk_vertices_le (f.1 0) s hw.2
  rw [← row_blocks_eq_visited_rows, ← col_blocks_eq_visited_cols, hr, hc, f.2, g.2] at hb
  exact hb

/-- Coefficients above the leading diagonal vanish identically, at every order. -/
theorem patternCoefficient_eq_zero_of_large (k r c : ℕ) (h : k + 1 < r + c) :
    patternCoefficient k r c = 0 := by
  letI : IsEmpty {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
      PatternSurvives k q.1 q.2 ∧ blockCount q.1 = r ∧ blockCount q.2 = c} :=
    ⟨fun q => by
      have hb := surviving_pattern_block_bound q.1.1 q.1.2 q.2.1
      rw [q.2.2.1, q.2.2.2] at hb
      omega⟩
  simp [patternCoefficient, Nat.card_eq_fintype_card]

end RandomMatrix
