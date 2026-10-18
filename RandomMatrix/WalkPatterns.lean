import RandomMatrix.Labelings
import RandomMatrix.WalkPositions

/-! Dimension-independent equality patterns for even closed alternating walks. -/

open scoped BigOperators Classical
namespace RandomMatrix

/-- The number of blocks of an equality pattern. -/
noncomputable def blockCount {α : Type*} (s : Setoid α) : ℕ := Nat.card (Quotient s)

/-- Closure and entry multiplicity parity expressed solely in terms of position partitions. -/
def PatternSurvives (k : ℕ) (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) : Prop :=
  r (Fin.last k) 0 ∧ ∀ e : Fin (k + 1) × Fin k,
    Even (((positionWord k).filter (fun d => decide (r d.1 e.1 ∧ c d.2 e.2))).length)

/-- The parity of a labeled word depends only on equality of its labels. -/
theorem even_map_iff_fibers {α β : Type*} [BEq β] [LawfulBEq β]
    (w : List α) (f : α → β) :
    (∀ b, Even ((w.map f).count b)) ↔
      ∀ a, Even ((w.filter (fun x => decide (f x = f a))).length) := by
  constructor
  · intro h a
    simpa only [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
      Bool.beq_eq_decide_eq, Function.comp_def, List.filter_map, List.length_map] using h (f a)
  · intro h b
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      simpa only [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
        Bool.beq_eq_decide_eq, Function.comp_def, List.filter_map, List.length_map] using h a
    · have hzero : (w.map f).count b = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
        exact hb ⟨a, ha⟩
      rw [hzero]
      exact ⟨0, rfl⟩

/-- Surviving concrete walks are precisely those whose equality patterns survive. -/
theorem isEvenClosedWalk_iff_pattern {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    IsEvenClosedWalk (i, s) ↔ PatternSurvives k
      (Setoid.ker (walkRowLabels i s)) (Setoid.ker (walkColLabels s)) := by
  unfold IsEvenClosedWalk PatternSurvives
  simp only [Setoid.ker_def, walkRowLabels_last, walkRowLabels_zero]
  apply and_congr_right
  intro _
  rw [← positionWord_map_labels i s, even_map_iff_fibers]
  simp only [Prod.mk.injEq]

/-- The exact number of even closed walks, grouped by their row and column partitions. -/
theorem evenClosedWalkCount_by_patterns (p n k : ℕ) :
    evenClosedWalkCount p n k =
      ∑ r : Setoid (Fin (k + 1)), ∑ c : Setoid (Fin k),
        if PatternSurvives k r c then
          p.descFactorial (blockCount r) * n.descFactorial (blockCount c) else 0 := by
  have hcount : evenClosedWalkCount p n k =
      ∑ w : Fin p × WalkSteps p n k, if IsEvenClosedWalk w then (1 : ℕ) else 0 := by
    rw [Finset.sum_boole]
    simp [evenClosedWalkCount, Fintype.card_subtype]
  rw [hcount]
  have hsum : (∑ w : Fin p × WalkSteps p n k, if IsEvenClosedWalk w then (1 : ℕ) else 0) =
      ∑ f : (Fin (k + 1) → Fin p) × (Fin k → Fin n),
        if PatternSurvives k (Setoid.ker f.1) (Setoid.ker f.2) then 1 else 0 := by
    apply Fintype.sum_equiv (walkLabelsEquiv p n k)
    intro w
    rcases w with ⟨i, s⟩
    change (if IsEvenClosedWalk (i, s) then (1 : ℕ) else 0) =
      if PatternSurvives k (Setoid.ker (walkRowLabels i s)) (Setoid.ker (walkColLabels s))
        then 1 else 0
    simp only [isEvenClosedWalk_iff_pattern]
  rw [hsum, Fintype.sum_prod_type]
  rw [sum_by_kernel_pair (R := Fin p) (C := Fin n) (F := fun r c => if PatternSurvives k r c then 1 else 0)]
  simp only [Fintype.card_fin, blockCount, ite_mul, one_mul, zero_mul]

/-- An exact all-order finite moment formula with dimension-independent pattern coefficients. -/
theorem expected_moment_by_patterns {p n : ℕ} (hp : 0 < p) (hn : 0 < n) (k : ℕ) :
    average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) =
      ((∑ r : Setoid (Fin (k + 1)), ∑ c : Setoid (Fin k),
        if PatternSurvives k r c then
          p.descFactorial (blockCount r) * n.descFactorial (blockCount c) else 0 : ℕ) : ℝ) /
        ((p : ℝ) * (n : ℝ) ^ k) := by
  rw [expected_moment_eq_walk_count hp hn, evenClosedWalkCount_by_patterns]

end RandomMatrix
