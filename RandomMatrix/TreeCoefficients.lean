import RandomMatrix.LeadingTreeBijection

/-! The bijection counts the original leading coefficients, retaining both color classes. -/

open scoped Classical
namespace RandomMatrix

/-- Leading equality patterns at a fixed moment order. -/
abbrev LeadingPatternsAt (k : ℕ) :=
  {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
    PatternSurvives k q.1 q.2 ∧ blockCount q.1 + blockCount q.2 = k + 1}

/-- Removing the redundant order field identifies the fixed-order pattern types. -/
def leadingPatternsAtEquiv (k : ℕ) :
    LeadingPatternsAt k ≃ {q : LeadingPattern // q.order = k} where
  toFun q := ⟨⟨k, q.val.1, q.val.2, q.property.1, q.property.2⟩, rfl⟩
  invFun q := by
    rcases q with ⟨⟨j, rows, cols, hs, hm⟩, hj⟩
    dsimp at hj
    subst j
    exact ⟨(rows, cols), hs, hm⟩
  left_inv q := by rfl
  right_inv q := by
    rcases q with ⟨⟨j, rows, cols, hs, hm⟩, hj⟩
    dsimp at hj
    subst j
    rfl

/-- At every order, including zero, leading patterns are exactly rooted ordered trees. -/
noncomputable def leadingPatternsTreeEquiv (k : ℕ) :
    LeadingPatternsAt k ≃ {t : OrderedTree // t.numNodes = k} :=
  (leadingPatternsAtEquiv k).trans
    (orderedTreeLeadingEquiv.subtypeEquiv (fun _ => Iff.rfl)).symm

/-- The coefficient's defining subtype agrees with the refined leading-pattern subtype. -/
def coefficientLeadingEquiv (k r c : ℕ) (h : r + c = k + 1) :
    {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
      PatternSurvives k q.1 q.2 ∧ blockCount q.1 = r ∧ blockCount q.2 = c} ≃
    {q : LeadingPattern // q.order = k ∧ blockCount q.rows = r ∧ blockCount q.cols = c} where
  toFun q := ⟨⟨k, q.val.1, q.val.2, q.property.1, by
    rw [q.property.2.1, q.property.2.2, h]⟩, rfl, q.property.2⟩
  invFun q := by
    rcases q with ⟨⟨j, rows, cols, hs, hm⟩, hp⟩
    have hj : j = k := hp.1
    subst j
    exact ⟨(rows, cols), hs, hp.2⟩
  left_inv q := by rfl
  right_inv q := by
    rcases q with ⟨⟨j, rows, cols, hs, hm⟩, hj, hr, hc⟩
    dsimp at hj
    subst j
    rfl

/-- The all-order equivalence preserves the number of row and column blocks separately. -/
noncomputable def refinedTreeLeadingEquiv (k r c : ℕ) :
    {t : OrderedTree // t.numNodes = k ∧ treeRows t = r ∧ treeCols t = c} ≃
    {q : LeadingPattern // q.order = k ∧ blockCount q.rows = r ∧ blockCount q.cols = c} :=
  orderedTreeLeadingEquiv.subtypeEquiv (fun t => by
    rw [(orderedTreeLeadingEquiv_counts t).2.1, (orderedTreeLeadingEquiv_counts t).2.2]
    rfl)

/-- The original leading moment coefficient counts ordered trees with the stated color counts. -/
noncomputable def coefficientTreeEquiv (k r c : ℕ) (h : r + c = k + 1) :
    {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
      PatternSurvives k q.1 q.2 ∧ blockCount q.1 = r ∧ blockCount q.2 = c} ≃
    {t : OrderedTree // t.numNodes = k ∧ treeRows t = r ∧ treeCols t = c} :=
  (coefficientLeadingEquiv k r c h).trans (refinedTreeLeadingEquiv k r c).symm

/-- Exact coefficient identity, before evaluating the tree count by a closed formula. -/
theorem patternCoefficient_eq_treeCount (k r c : ℕ) (h : r + c = k + 1) :
    patternCoefficient k r c =
      Nat.card {t : OrderedTree // t.numNodes = k ∧ treeRows t = r ∧ treeCols t = c} :=
  Nat.card_congr (coefficientTreeEquiv k r c h)

end RandomMatrix
