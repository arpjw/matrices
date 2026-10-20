import RandomMatrix.NarayanaTreeCount

/-! The Narayana formula for the original leading coefficients of finite covariance moments. -/

namespace RandomMatrix

/-- On the leading diagonal, the row count determines the column count. -/
theorem patternCoefficient_cast_eq_rowTreePoly (k r c : ℕ) (h : r + c = k + 1) :
    (patternCoefficient k r c : ℚ) = (rowTreePoly k).coeff r := by
  rw [patternCoefficient_eq_treeCount k r c h, rowTreePoly_coeff_card]
  congr 1
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  constructor
  · exact fun ht => ⟨ht.1, ht.2.1⟩
  · rintro ⟨hk, hr⟩
    have hv := tree_vertex_counts t
    exact ⟨hk, hr, by omega⟩

/-- The general rational Narayana formula for every positive-order leading coefficient. -/
theorem patternCoefficient_narayana_rat (k r c : ℕ) (hk : 0 < k) (hr : 0 < r)
    (h : r + c = k + 1) :
    (patternCoefficient k r c : ℚ) = (k.choose r : ℚ) * k.choose (r - 1) / k := by
  rw [patternCoefficient_cast_eq_rowTreePoly k r c h, rowTreePoly_coeff_narayana k r hk]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr)
  simpa using narayanaQ_pos k j hk

/-- The binomial product is exactly k times the integer pattern count; no rounding is used. -/
theorem mul_patternCoefficient_narayana (k r c : ℕ) (hk : 0 < k) (hr : 0 < r)
    (h : r + c = k + 1) :
    k * patternCoefficient k r c = k.choose r * k.choose (r - 1) := by
  have hh := patternCoefficient_narayana_rat k r c hk hr h
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  have hm := (eq_div_iff hkq).mp hh
  exact_mod_cast (mul_comm (k : ℚ) (patternCoefficient k r c)).trans hm

/-- Closed natural-number formula for the original leading moment coefficient. -/
theorem patternCoefficient_narayana (k r c : ℕ) (hk : 0 < k) (hr : 0 < r)
    (h : r + c = k + 1) :
    patternCoefficient k r c = k.choose r * k.choose (r - 1) / k := by
  rw [← mul_patternCoefficient_narayana k r c hk hr h]
  simp [ne_of_gt hk]

/-- The usual row-indexed form of the Narayana identity. -/
theorem leadingCoefficient_narayana (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) :
    patternCoefficient k r (k + 1 - r) = k.choose r * k.choose (r - 1) / k :=
  patternCoefficient_narayana k r (k + 1 - r) (by omega) (by omega) (by omega)

/-- Summing over the color refinement gives the Catalan number of all leading patterns. -/
theorem leadingPatterns_card_catalan (k : ℕ) : Nat.card (LeadingPatternsAt k) = catalan k := by
  calc
    _ = Nat.card {t : OrderedTree // t.numNodes = k} :=
      Nat.card_congr (leadingPatternsTreeEquiv k)
    _ = Nat.card ↥(Tree.treesOfNumNodesEq k) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun t => by simp))
    _ = (Tree.treesOfNumNodesEq k).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = catalan k := Tree.treesOfNumNodesEq_card_eq_catalan k

end RandomMatrix
