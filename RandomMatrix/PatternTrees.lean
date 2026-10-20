import RandomMatrix.PatternGraph

/-! Leading patterns are precisely closed traversals of trees using each edge twice. -/

open scoped BigOperators Classical
namespace RandomMatrix

theorem positionWord_length (k : ℕ) : (positionWord k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [positionWord, ih]; omega

theorem patternWord_length {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) :
    (patternWord r c).length = 2 * k := by
  simp [patternWord, positionWord_length]

/-- Survival gives even multiplicity directly on quotient-block edges. -/
theorem patternWord_even {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k))
    (h : PatternSurvives k r c) (e : Quotient r × Quotient c) :
    Even ((patternWord r c).count e) := by
  apply (even_map_iff_fibers (positionWord k)
    (fun d => (Quotient.mk r d.1, Quotient.mk c d.2))).mpr
  simpa only [Prod.mk.injEq, Quotient.eq] using h.2

theorem patternWord_closed {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k))
    (h : PatternSurvives k r c) :
    Quotient.mk r (Fin.last k) = Quotient.mk r 0 :=
  Quotient.sound h.1

/-- The original survival predicate agrees exactly with closure and parity on block labels. -/
theorem patternSurvives_iff_closed_even {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) :
    PatternSurvives k r c ↔ Quotient.mk r (Fin.last k) = Quotient.mk r 0 ∧
      ∀ e, Even ((patternWord r c).count e) := by
  constructor
  · intro h
    exact ⟨patternWord_closed r c h, patternWord_even r c h⟩
  · rintro ⟨hc, he⟩
    refine ⟨Quotient.exact hc, ?_⟩
    have hf := (even_map_iff_fibers (positionWord k)
      (fun d => (Quotient.mk r d.1, Quotient.mk c d.2))).mp he
    simpa only [Prod.mk.injEq, Quotient.eq] using hf

/-- A closed pattern using every visited edge twice survives the sign expectation. -/
theorem closed_doubled_pattern_survives {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (hc : Quotient.mk r (Fin.last k) = Quotient.mk r 0)
    (htwice : ∀ e ∈ patternWord r c, (patternWord r c).count e = 2) :
    PatternSurvives k r c := by
  apply (patternSurvives_iff_closed_even r c).mpr
  refine ⟨hc, fun e => ?_⟩
  by_cases he : e ∈ patternWord r c
  · rw [htwice e he]
    exact ⟨1, rfl⟩
  · rw [List.count_eq_zero.mpr he]
    exact ⟨0, rfl⟩

theorem surviving_pattern_edges_le {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    (patternEdges r c).card ≤ k := by
  have hb := even_word_support_bound (patternWord r c) (patternWord_even r c h)
  rw [patternWord_length] at hb
  change (patternWord r c).toFinset.card ≤ k
  omega

/-- A leading pattern has exactly k distinct entries. -/
theorem maximal_pattern_edge_card {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c)
    (hmax : blockCount r + blockCount c = k + 1) :
    (patternEdges r c).card = k := by
  have hlo := (patternGraph_connected r c).card_vert_le_card_edgeSet_add_one
  rw [patternGraph_vertex_card, patternGraph_edge_card, hmax] at hlo
  have hhi := surviving_pattern_edges_le r c h
  omega

/-- Equality in the vertex bound forces the actual quotient-block graph to be a tree. -/
theorem maximal_pattern_isTree {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c)
    (hmax : blockCount r + blockCount c = k + 1) : (patternGraph r c).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨patternGraph_connected r c, ?_⟩
  rw [patternGraph_edge_card, patternGraph_vertex_card, maximal_pattern_edge_card r c h hmax,
    hmax]

/-- Each edge of a leading pattern occurs exactly twice in its position word. -/
theorem maximal_pattern_edges_twice {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c)
    (hmax : blockCount r + blockCount c = k + 1)
    (e : Quotient r × Quotient c) (he : e ∈ patternWord r c) :
    (patternWord r c).count e = 2 := by
  apply even_word_maximal_support (patternWord r c) (patternWord_even r c h) _ e he
  rw [patternWord_length]
  change 2 * k = 2 * (patternEdges r c).card
  rw [maximal_pattern_edge_card r c h hmax]

/-- A tree with every entry used twice has the maximal number of blocks. -/
theorem doubled_tree_pattern_maximal {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (ht : (patternGraph r c).IsTree)
    (htwice : ∀ e ∈ patternWord r c, (patternWord r c).count e = 2) :
    blockCount r + blockCount c = k + 1 := by
  have hlength : ∑ e ∈ (patternWord r c).toFinset, (patternWord r c).count e =
      (patternWord r c).length := by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      List.sum_toFinset_count_eq_length (patternWord r c)
  have hsum : (∑ e ∈ (patternWord r c).toFinset, (patternWord r c).count e) =
      2 * (patternEdges r c).card := by
    calc
      _ = ∑ _e ∈ (patternWord r c).toFinset, (2 : ℕ) :=
        Finset.sum_congr rfl (fun e he => htwice e (List.mem_toFinset.mp he))
      _ = _ := by simp [patternEdges, Nat.mul_comm]
  rw [patternWord_length, hsum] at hlength
  have hcard := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  rw [patternGraph_edge_card, patternGraph_vertex_card] at hcard
  omega

/-- The full leading-pattern characterization; the double-traversal condition is essential. -/
theorem maximal_pattern_iff_doubled_tree {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    blockCount r + blockCount c = k + 1 ↔
      (patternGraph r c).IsTree ∧
        ∀ e ∈ patternWord r c, (patternWord r c).count e = 2 := by
  exact ⟨fun hm => ⟨maximal_pattern_isTree r c h hm, maximal_pattern_edges_twice r c h hm⟩,
    fun ht => doubled_tree_pattern_maximal r c ht.1 ht.2⟩

/-- A characterization with no survival assumption, suitable for constructing leading patterns. -/
theorem leading_pattern_iff_closed_doubled_tree {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) :
    (PatternSurvives k r c ∧ blockCount r + blockCount c = k + 1) ↔
      (Quotient.mk r (Fin.last k) = Quotient.mk r 0 ∧
        (patternGraph r c).IsTree ∧
          ∀ e ∈ patternWord r c, (patternWord r c).count e = 2) := by
  constructor
  · rintro ⟨h, hm⟩
    exact ⟨patternWord_closed r c h, (maximal_pattern_iff_doubled_tree r c h).mp hm⟩
  · rintro ⟨hc, ht, htwice⟩
    exact ⟨closed_doubled_pattern_survives r c hc htwice,
      doubled_tree_pattern_maximal r c ht htwice⟩

end RandomMatrix
