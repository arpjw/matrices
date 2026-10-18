import RandomMatrix.Walks

/-! The number of distinct row and column vertices in an even alternating walk. -/

namespace RandomMatrix

/-- Rows visited by a walk, including its initial row even at order zero. -/
def walkRows {p n : ℕ} : {k : ℕ} → Fin p → WalkSteps p n k → Finset (Fin p)
  | 0, i, _ => {i}
  | _ + 1, i, s => insert i (walkRows s.1 s.2.2)

/-- Columns visited by a walk. -/
def walkCols {p n : ℕ} : {k : ℕ} → Fin p → WalkSteps p n k → Finset (Fin n)
  | 0, _, _ => ∅
  | _ + 1, _, s => insert s.2.1 (walkCols s.1 s.2.2)

theorem start_mem_walkRows {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    i ∈ walkRows i s := by
  cases k <;> simp [walkRows]

theorem walkWord_mem_vertices {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k)
    (e : Fin p × Fin n) (he : e ∈ walkWord i s) :
    e.1 ∈ walkRows i s ∧ e.2 ∈ walkCols i s := by
  induction k generalizing i with
  | zero => simp [walkWord] at he
  | succ k ih =>
    simp only [walkWord, List.mem_cons] at he
    rcases he with rfl | rfl | he
    · simp [walkRows, walkCols]
    · simp [walkRows, walkCols, start_mem_walkRows]
    · exact ⟨Finset.mem_insert_of_mem (ih s.1 s.2.2 he).1,
        Finset.mem_insert_of_mem (ih s.1 s.2.2 he).2⟩

/-- Adding a two-edge segment can introduce no more vertices than new edges. -/
private theorem extend_card_bound {P N : Type*} [DecidableEq P] [DecidableEq N]
    (R : Finset P) (C : Finset N) (E : Finset (P × N))
    (j : P) (hj : j ∈ R)
    (hE : ∀ e ∈ E, e.1 ∈ R ∧ e.2 ∈ C)
    (h : R.card + C.card ≤ E.card + 1) (i : P) (a : N) :
    (insert i R).card + (insert a C).card ≤
      (insert (i, a) (insert (j, a) E)).card + 1 := by
  have hsub : E.card ≤ (insert (i, a) (insert (j, a) E)).card :=
    Finset.card_le_card ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))
  by_cases hi : i ∈ R
  · by_cases ha : a ∈ C
    · simpa [Finset.insert_eq_of_mem hi, Finset.insert_eq_of_mem ha] using h.trans (by omega)
    · have hja : (j, a) ∉ E := fun he => ha (hE (j, a) he).2
      have hnew := Finset.card_le_card (Finset.subset_insert (i, a) (insert (j, a) E))
      rw [Finset.card_insert_of_notMem hja] at hnew
      rw [Finset.card_insert_of_mem hi, Finset.card_insert_of_notMem ha]
      omega
  · have hij : i ≠ j := fun hij => hi (hij ▸ hj)
    have hia : (i, a) ∉ E := fun he => hi (hE (i, a) he).1
    have hia' : (i, a) ∉ insert (j, a) E := by simp [hia, hij]
    rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hia']
    by_cases ha : a ∈ C
    · rw [Finset.card_insert_of_mem ha]
      have hnew := Finset.card_le_card (Finset.subset_insert (j, a) E)
      omega
    · have hja : (j, a) ∉ E := fun he => ha (hE (j, a) he).2
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hja]
      omega

/-- The visited bipartite graph is connected: vertices are at most edges plus one. -/
theorem walk_vertices_le_edges_add_one {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    (walkRows i s).card + (walkCols i s).card ≤ (walkWord i s).toFinset.card + 1 := by
  induction k generalizing i with
  | zero => simp [walkRows, walkCols, walkWord]
  | succ k ih =>
    simp only [walkRows, walkCols, walkWord, List.toFinset_cons]
    exact extend_card_bound _ _ _ s.1 (start_mem_walkRows s.1 s.2.2)
      (fun e he => walkWord_mem_vertices s.1 s.2.2 e (List.mem_toFinset.mp he))
      (ih s.1 s.2.2) i s.2.1

/-- Every distinct coordinate in an even word consumes at least two positions. -/
theorem even_word_support_bound {ι : Type*} [DecidableEq ι] [BEq ι] [LawfulBEq ι] (w : List ι)
    (heven : ∀ e, Even (w.count e)) : 2 * w.toFinset.card ≤ w.length := by
  have hcount : ∀ e ∈ w.toFinset, 2 ≤ w.count e := by
    intro e he
    have hpos := List.count_pos_iff.mpr (List.mem_toFinset.mp he)
    obtain ⟨m, hm⟩ := heven e
    omega
  have hsum := Finset.sum_le_sum hcount
  have hlength : ∑ e ∈ w.toFinset, w.count e = w.length := by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      List.sum_toFinset_count_eq_length w
  simpa [hlength, Nat.mul_comm] using hsum

/-- An even walk of order k uses at most k distinct matrix-entry coordinates. -/
theorem even_walk_edges_le {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k)
    (heven : ∀ e, Even ((walkWord i s).count e)) :
    (walkWord i s).toFinset.card ≤ k := by
  have h := even_word_support_bound (walkWord i s) heven
  rw [walkWord_length] at h
  omega

/-- The all-order r+c ≤ k+1 bound for surviving walks. Closure is not needed for the bound. -/
theorem even_walk_vertices_le {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k)
    (heven : ∀ e, Even ((walkWord i s).count e)) :
    (walkRows i s).card + (walkCols i s).card ≤ k + 1 := by
  exact (walk_vertices_le_edges_add_one i s).trans (Nat.add_le_add_right
    (even_walk_edges_le i s heven) 1)

/-- At maximal support size, every coordinate that occurs in an even word occurs twice. -/
theorem even_word_maximal_support {ι : Type*} [DecidableEq ι] [BEq ι] [LawfulBEq ι]
    (w : List ι) (heven : ∀ e, Even (w.count e))
    (hsize : w.length = 2 * w.toFinset.card) (e : ι) (he : e ∈ w) : w.count e = 2 := by
  have hcount : ∀ a ∈ w.toFinset, 2 ≤ w.count a := by
    intro a ha
    have hpos := List.count_pos_iff.mpr (List.mem_toFinset.mp ha)
    obtain ⟨m, hm⟩ := heven a
    omega
  have hlength : ∑ a ∈ w.toFinset, w.count a = w.length := by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      List.sum_toFinset_count_eq_length w
  have hsum : (∑ _a ∈ w.toFinset, (2 : ℕ)) = ∑ a ∈ w.toFinset, w.count a := by
    simp [hlength, hsize, Nat.mul_comm]
  exact ((Finset.sum_eq_sum_iff_of_le hcount).mp hsum e (List.mem_toFinset.mpr he)).symm

/-- Saturating r+c ≤ k+1 forces every used matrix entry to appear exactly twice. -/
theorem maximal_even_walk_edges_twice {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k)
    (heven : ∀ e, Even ((walkWord i s).count e))
    (hmax : (walkRows i s).card + (walkCols i s).card = k + 1)
    (e : Fin p × Fin n) (he : e ∈ walkWord i s) : (walkWord i s).count e = 2 := by
  have hgraph := walk_vertices_le_edges_add_one i s
  have hedge := even_walk_edges_le i s heven
  have hcard : (walkWord i s).toFinset.card = k := by omega
  apply even_word_maximal_support (walkWord i s) heven _ e he
  rw [walkWord_length, hcard]

end RandomMatrix
