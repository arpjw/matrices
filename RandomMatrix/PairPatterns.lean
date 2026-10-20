import RandomMatrix.PatternGraph

/-! Joint equality patterns for two walks, and their connected support bound. -/

open scoped Classical
namespace RandomMatrix

abbrev PairRows (k : ℕ) := Fin (k + 1) ⊕ Fin (k + 1)
abbrev PairCols (k : ℕ) := Fin k ⊕ Fin k

def pairPositionWord (k : ℕ) : List (PairRows k × PairCols k) :=
  (positionWord k).map (fun e => (Sum.inl e.1, Sum.inl e.2)) ++
  (positionWord k).map (fun e => (Sum.inr e.1, Sum.inr e.2))

/-- A convenient superset of covariance-contributing pairs: shared row and joint parity.
Closure is not needed for the upper bound. -/
def PairPatternSurvives (k : ℕ) (r : Setoid (PairRows k)) (c : Setoid (PairCols k)) : Prop :=
  (∃ i j, r (Sum.inl i) (Sum.inr j)) ∧
  ∀ e : PairRows k × PairCols k,
    Even (((pairPositionWord k).filter (fun d => decide (r d.1 e.1 ∧ c d.2 e.2))).length)

def pairPatternWord {k : ℕ} (r : Setoid (PairRows k)) (c : Setoid (PairCols k)) :
    List (Quotient r × Quotient c) :=
  (pairPositionWord k).map (fun e => (Quotient.mk r e.1, Quotient.mk c e.2))

noncomputable def pairPatternGraph {k : ℕ} (r : Setoid (PairRows k)) (c : Setoid (PairCols k)) :
    SimpleGraph (Quotient r ⊕ Quotient c) :=
  bipartiteEntryGraph ((pairPatternWord r c).toFinset : Set (Quotient r × Quotient c))

theorem positionWord_length (k : ℕ) : (positionWord k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [positionWord, ih]; omega

theorem pairPositionWord_length (k : ℕ) : (pairPositionWord k).length = 4 * k := by
  simp [pairPositionWord, positionWord_length]
  omega

private theorem pairGraph_adj {k : ℕ} (r : Setoid (PairRows k)) (c : Setoid (PairCols k))
    (e : PairRows k × PairCols k) (he : e ∈ pairPositionWord k) :
    (pairPatternGraph r c).Adj (.inl (Quotient.mk r e.1)) (.inr (Quotient.mk c e.2)) := by
  change (Quotient.mk r e.1, Quotient.mk c e.2) ∈ (pairPatternWord r c).toFinset
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)

private theorem pairPositionWord_left {k : ℕ} (e : Fin (k + 1) × Fin k)
    (he : e ∈ positionWord k) : (Sum.inl e.1, Sum.inl e.2) ∈ pairPositionWord k := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)

private theorem pairPositionWord_right {k : ℕ} (e : Fin (k + 1) × Fin k)
    (he : e ∈ positionWord k) : (Sum.inr e.1, Sum.inr e.2) ∈ pairPositionWord k := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- A common row joins the two alternating position walks into one connected graph. -/
theorem pairPatternGraph_connected {k : ℕ} (r : Setoid (PairRows k)) (c : Setoid (PairCols k))
    (hshare : ∃ i j, r (Sum.inl i) (Sum.inr j)) : (pairPatternGraph r c).Connected := by
  let rootL : Quotient r ⊕ Quotient c := .inl (Quotient.mk r (Sum.inl 0))
  let rootR : Quotient r ⊕ Quotient c := .inl (Quotient.mk r (Sum.inr 0))
  have hL (j : Fin (k + 1)) :
      (pairPatternGraph r c).Reachable rootL (.inl (Quotient.mk r (Sum.inl j))) := by
    induction j using Fin.induction with
    | zero => exact .refl _
    | succ j ih =>
      exact ih.trans ((pairGraph_adj r c _ (pairPositionWord_left _ (positionWord_left_mem j))).reachable.trans
        (pairGraph_adj r c _ (pairPositionWord_left _ (positionWord_right_mem j))).symm.reachable)
  have hR (j : Fin (k + 1)) :
      (pairPatternGraph r c).Reachable rootR (.inl (Quotient.mk r (Sum.inr j))) := by
    induction j using Fin.induction with
    | zero => exact .refl _
    | succ j ih =>
      exact ih.trans ((pairGraph_adj r c _ (pairPositionWord_right _ (positionWord_left_mem j))).reachable.trans
        (pairGraph_adj r c _ (pairPositionWord_right _ (positionWord_right_mem j))).symm.reachable)
  obtain ⟨i, j, hij⟩ := hshare
  have heq : Quotient.mk r (Sum.inl i) = Quotient.mk r (Sum.inr j) := Quotient.sound hij
  have hroots : (pairPatternGraph r c).Reachable rootL rootR := by
    have h := hL i
    rw [heq] at h
    exact h.trans (hR j).symm
  have hall (v : Quotient r ⊕ Quotient c) : (pairPatternGraph r c).Reachable rootL v := by
    rcases v with v | v
    · induction v using Quotient.inductionOn with
      | h x =>
        rcases x with x | x
        · exact hL x
        · exact hroots.trans (hR x)
    · induction v using Quotient.inductionOn with
      | h x =>
        rcases x with x | x
        · exact (hL x.castSucc).trans
            (pairGraph_adj r c _ (pairPositionWord_left _ (positionWord_left_mem x))).reachable
        · exact (hroots.trans (hR x.castSucc)).trans
            (pairGraph_adj r c _ (pairPositionWord_right _ (positionWord_left_mem x))).reachable
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨rootL, hall⟩

/-- Joint parity limits the connected pair graph to 2k+1 vertices. -/
theorem pair_surviving_block_bound {k : ℕ} (r : Setoid (PairRows k)) (c : Setoid (PairCols k))
    (h : PairPatternSurvives k r c) : blockCount r + blockCount c ≤ 2 * k + 1 := by
  have heven : ∀ e, Even ((pairPatternWord r c).count e) := by
    rw [pairPatternWord, even_map_iff_fibers]
    simpa only [Prod.mk.injEq, Quotient.eq] using h.2
  have hedge := even_word_support_bound (pairPatternWord r c) heven
  have hlen : (pairPatternWord r c).length = 4 * k := by
    simp [pairPatternWord, pairPositionWord_length]
  rw [hlen] at hedge
  have hv := (pairPatternGraph_connected r c h.1).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_sum, show Nat.card (pairPatternGraph r c).edgeSet =
    (pairPatternWord r c).toFinset.card from entryGraph_edge_card _] at hv
  change blockCount r + blockCount c ≤ _ at hv
  omega

theorem pair_row_blocks_pos {k : ℕ} (r : Setoid (PairRows k)) : 0 < blockCount r := by
  unfold blockCount
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos

/-- The concrete predicate is exactly its kernel-partition predicate. -/
theorem pair_survives_kernel_iff {p n k : ℕ} (f : PairRows k → Fin p) (g : PairCols k → Fin n) :
    PairPatternSurvives k (Setoid.ker f) (Setoid.ker g) ↔
      (∃ i j, f (Sum.inl i) = f (Sum.inr j)) ∧
      (∀ e, Even (((pairPositionWord k).map (fun d => (f d.1, g d.2))).count e)) := by
  rw [PairPatternSurvives, even_map_iff_fibers]
  simp only [Setoid.ker_def, Prod.mk.injEq]

end RandomMatrix
