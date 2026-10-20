import RandomMatrix.PairPatterns

/-! Exact regrouping of the covariance upper-bound count by joint equality patterns. -/

open scoped BigOperators Classical
namespace RandomMatrix

/-- Two rooted walks are exactly joint row and column label assignments. -/
def pairWalkLabelsEquiv (p n k : ℕ) :
    ((Fin p × WalkSteps p n k) × (Fin p × WalkSteps p n k)) ≃
      ((PairRows k → Fin p) × (PairCols k → Fin n)) where
  toFun w :=
    (Sum.elim (walkLabelsEquiv p n k w.1).1 (walkLabelsEquiv p n k w.2).1,
     Sum.elim (walkLabelsEquiv p n k w.1).2 (walkLabelsEquiv p n k w.2).2)
  invFun f :=
    ((walkLabelsEquiv p n k).symm (f.1 ∘ Sum.inl, f.2 ∘ Sum.inl),
     (walkLabelsEquiv p n k).symm (f.1 ∘ Sum.inr, f.2 ∘ Sum.inr))
  left_inv w := by
    change ((walkLabelsEquiv p n k).symm (walkLabelsEquiv p n k w.1),
      (walkLabelsEquiv p n k).symm (walkLabelsEquiv p n k w.2)) = w
    simp
  right_inv f := by
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext <;> funext x <;> cases x <;> rfl

theorem pairPositionWord_map_labels {p n k : ℕ}
    (w : (Fin p × WalkSteps p n k) × (Fin p × WalkSteps p n k)) :
    (pairPositionWord k).map (fun e =>
      ((pairWalkLabelsEquiv p n k w).1 e.1, (pairWalkLabelsEquiv p n k w).2 e.2)) =
      walkWord w.1.1 w.1.2 ++ walkWord w.2.1 w.2.2 := by
  simp only [pairPositionWord, List.map_append, List.map_map, pairWalkLabelsEquiv,
    walkLabelsEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr, Function.comp_def]
  rw [positionWord_map_labels, positionWord_map_labels]

noncomputable def pairWalkCount (p n k : ℕ) : ℕ :=
  ∑ w : (Fin p × WalkSteps p n k) × (Fin p × WalkSteps p n k),
    if PairPatternSurvives k (Setoid.ker (pairWalkLabelsEquiv p n k w).1)
      (Setoid.ker (pairWalkLabelsEquiv p n k w).2) then 1 else 0

/-- The upper-bound count has exact falling-factorial labeling multiplicities. -/
theorem pairWalkCount_by_patterns (p n k : ℕ) :
    pairWalkCount p n k =
      ∑ r : Setoid (PairRows k), ∑ c : Setoid (PairCols k),
        if PairPatternSurvives k r c then
          p.descFactorial (blockCount r) * n.descFactorial (blockCount c) else 0 := by
  unfold pairWalkCount
  rw [Equiv.sum_comp (pairWalkLabelsEquiv p n k)
    (fun f => if PairPatternSurvives k (Setoid.ker f.1) (Setoid.ker f.2) then (1 : ℕ) else 0)]
  rw [Fintype.sum_prod_type]
  rw [sum_by_kernel_pair (R := Fin p) (C := Fin n)
    (F := fun r c => if PairPatternSurvives k r c then 1 else 0)]
  simp only [Fintype.card_fin, blockCount, ite_mul, one_mul, zero_mul]

end RandomMatrix
