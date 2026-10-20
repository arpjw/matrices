import RandomMatrix.PatternTrees

/-! Realizing the ordered position word as a walk in the quotient-block graph. -/

open scoped Classical
namespace RandomMatrix

/-- The successive row-column-row steps as a genuine graph walk. -/
def positionGraphWalk {R C : Type*} (G : SimpleGraph (R ⊕ C)) :
    {k : ℕ} → (r : Fin (k + 1) → R) → (c : Fin k → C) →
      (∀ e ∈ positionWord k, G.Adj (.inl (r e.1)) (.inr (c e.2))) →
      G.Walk (.inl (r 0)) (.inl (r (Fin.last k)))
  | 0, _, _, _ => .nil
  | k + 1, r, c, h =>
    .cons (h (0, 0) (by simp [positionWord]))
      (.cons (h (1, 0) (by simp [positionWord])).symm
        (positionGraphWalk G (fun j => r j.succ) (fun j => c j.succ)
          (fun e he => h (e.1.succ, e.2.succ) (by
            simp only [positionWord, List.mem_cons, List.mem_map]
            exact Or.inr (Or.inr ⟨e, he, rfl⟩)))))

/-- The graph walk retains exactly the original order of the entry visits. -/
theorem positionGraphWalk_edges {R C : Type*} (G : SimpleGraph (R ⊕ C)) {k : ℕ}
    (r : Fin (k + 1) → R) (c : Fin k → C)
    (h : ∀ e ∈ positionWord k, G.Adj (.inl (r e.1)) (.inr (c e.2))) :
    (positionGraphWalk G r c h).edges =
      (positionWord k).map (fun e => s(Sum.inl (r e.1), Sum.inr (c e.2))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [positionGraphWalk, SimpleGraph.Walk.edges_cons, ih, positionWord,
      List.map_cons, List.map_map, Function.comp_def]
    congr 1
    congr 1
    exact Sym2.eq_swap

/-- The pattern's entry order is realized without choosing representative labels. -/
noncomputable def patternGraphWalk {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) :
    (patternGraph r c).Walk (.inl (Quotient.mk r 0)) (.inl (Quotient.mk r (Fin.last k))) :=
  positionGraphWalk (patternGraph r c) (Quotient.mk r) (Quotient.mk c)
    (patternGraph_adj_of_position r c)

theorem patternGraphWalk_edges {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) :
    (patternGraphWalk r c).edges =
      (patternWord r c).map (fun e => s(Sum.inl e.1, Sum.inr e.2)) := by
  rw [patternGraphWalk, positionGraphWalk_edges]
  simp [patternWord, List.map_map]

theorem patternGraphWalk_length {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) : (patternGraphWalk r c).length = 2 * k := by
  rw [← SimpleGraph.Walk.length_edges, patternGraphWalk_edges, List.length_map, patternWord_length]

/-- Survival closes the genuine graph walk at its distinguished row root. -/
noncomputable def patternClosedGraphWalk {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    (patternGraph r c).Walk (.inl (Quotient.mk r 0)) (.inl (Quotient.mk r 0)) :=
  (patternGraphWalk r c).copy rfl (congrArg Sum.inl (patternWord_closed r c h))

theorem patternClosedGraphWalk_edges {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    (patternClosedGraphWalk r c h).edges =
      (patternWord r c).map (fun e => s(Sum.inl e.1, Sum.inr e.2)) := by
  simp [patternClosedGraphWalk, patternGraphWalk_edges]

theorem patternClosedGraphWalk_length {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    (patternClosedGraphWalk r c h).length = 2 * k := by
  simp [patternClosedGraphWalk, patternGraphWalk_length]

/-- The actual closed tree walk visits each of its undirected edges exactly twice. -/
theorem maximal_patternClosedGraphWalk_edges_twice {k : ℕ}
    (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) (h : PatternSurvives k r c)
    (hmax : blockCount r + blockCount c = k + 1)
    (e : Sym2 (Quotient r ⊕ Quotient c)) (he : e ∈ (patternClosedGraphWalk r c h).edges) :
    (patternClosedGraphWalk r c h).edges.count e = 2 := by
  rw [patternClosedGraphWalk_edges] at he ⊢
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have hinj : Function.Injective
      (fun d : Quotient r × Quotient c => s(Sum.inl d.1, Sum.inr d.2)) := by
    intro a b hab
    simpa only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, and_self, or_false, Prod.ext_iff] using hab
  rw [List.count_map_of_injective _ _ hinj]
  exact maximal_pattern_edges_twice r c h hmax d hd

end RandomMatrix
