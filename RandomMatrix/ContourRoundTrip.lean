import RandomMatrix.ContourPatterns

/-! Recovering the original ordered word and equality partitions without choosing block names. -/

open scoped Classical
open SimpleGraph SimpleGraph.Walk
namespace RandomMatrix

theorem positionGraphWalk_positions {R C : Type*} (G : SimpleGraph (R ⊕ C)) {k : ℕ}
    (r : Fin (k + 1) → R) (c : Fin k → C)
    (h : ∀ e ∈ positionWord k, G.Adj (.inl (r e.1)) (.inr (c e.2))) :
    evenPositions (positionGraphWalk G r c h).support = List.ofFn (fun j => Sum.inl (r j)) ∧
      oddPositions (positionGraphWalk G r c h).support = List.ofFn (fun j => Sum.inr (c j)) := by
  induction k with
  | zero =>
    simp [positionGraphWalk, evenPositions, oddPositions, List.ofFn_succ]
  | succ k ih =>
    have hh := ih (fun j => r j.succ) (fun j => c j.succ)
      (fun e he => h (e.1.succ, e.2.succ) (by
        simp only [positionWord, List.mem_cons, List.mem_map]
        exact Or.inr (Or.inr ⟨e, he, rfl⟩)))
    simp only [positionGraphWalk, support_cons, evenPositions_cons, oddPositions_cons,
      hh.1, hh.2, List.ofFn_succ]
    exact ⟨trivial, trivial⟩

theorem patternGraphWalk_positions {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) :
    evenPositions (patternGraphWalk r c).support =
        List.ofFn (fun j => Sum.inl (Quotient.mk r j)) ∧
      oddPositions (patternGraphWalk r c).support =
        List.ofFn (fun j => Sum.inr (Quotient.mk c j)) :=
  positionGraphWalk_positions _ _ _ _

theorem patternClosedGraphWalk_positions {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    evenPositions (patternClosedGraphWalk r c h).support =
        List.ofFn (fun j => Sum.inl (Quotient.mk r j)) ∧
      oddPositions (patternClosedGraphWalk r c h).support =
        List.ofFn (fun j => Sum.inr (Quotient.mk c j)) := by
  simpa only [patternClosedGraphWalk, support_copy] using patternGraphWalk_positions r c

theorem patternClosedGraphWalk_tail_length {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    (patternClosedGraphWalk r c h).support.tail.length = 2 * k := by
  rw [List.length_tail, length_support, patternClosedGraphWalk_length]
  omega

/-- Taking the two equality partitions of the graph contour recovers the original pattern. -/
theorem patternClosedGraphWalk_pattern {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (h : PatternSurvives k r c) :
    contourPattern (Sum.inl (Quotient.mk r 0)) (patternClosedGraphWalk r c h).support.tail
      (patternClosedGraphWalk_tail_length r c h) = (r, c) := by
  have hs := (support_eq_cons (patternClosedGraphWalk r c h)).symm
  have hp := patternClosedGraphWalk_positions r c h
  have hr : contourRowLabels (Sum.inl (Quotient.mk r 0))
      (patternClosedGraphWalk r c h).support.tail
      (patternClosedGraphWalk_tail_length r c h) = fun j => Sum.inl (Quotient.mk r j) := by
    funext j
    simp only [contourRowLabels, listLabels, hs, hp.1, List.getElem_ofFn]
  have hc : contourColLabels (Sum.inl (Quotient.mk r 0))
      (patternClosedGraphWalk r c h).support.tail
      (patternClosedGraphWalk_tail_length r c h) = fun j => Sum.inr (Quotient.mk c j) := by
    funext j
    simp only [contourColLabels, listLabels, hs, hp.2, List.getElem_ofFn]
  apply Prod.ext
  · apply Setoid.ext
    intro a b
    simp only [contourPattern, Setoid.ker_def, hr, Sum.inl.injEq, Quotient.eq]
  · apply Setoid.ext
    intro a b
    simp only [contourPattern, Setoid.ker_def, hc, Sum.inr.injEq, Quotient.eq]

/-- Interpreting the quotient blocks as their original labels recovers the full ordered word. -/
theorem contourPattern_graphWalk_map {V : Type*} {k : ℕ} (u : V) (w : List V)
    (h : w.length = 2 * k)
    (hd : Disjoint (Set.range (contourRowLabels u w h)) (Set.range (contourColLabels u w h))) :
    (patternGraphWalk (contourPattern u w h).1 (contourPattern u w h).2).support.map
      (labelSumEmbedding (contourRowLabels u w h) (contourColLabels u w h) hd) = u :: w := by
  let emb := labelSumEmbedding (contourRowLabels u w h) (contourColLabels u w h) hd
  apply positions_injective
  · rw [(positions_map emb _).1, (patternGraphWalk_positions _ _).1, List.map_ofFn]
    change List.ofFn (contourRowLabels u w h) = evenPositions (u :: w)
    exact listLabels_toList _ _
  · rw [(positions_map emb _).2, (patternGraphWalk_positions _ _).2, List.map_ofFn]
    change List.ofFn (contourColLabels u w h) = oddPositions (u :: w)
    exact listLabels_toList _ _

theorem IsOrderedContour.graphWalk_map {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) :
    (patternClosedGraphWalk (contourPattern u w h.length).1 (contourPattern u w h.length).2
      h.pattern_leading.1).support.tail.map
        (labelSumEmbedding (contourRowLabels u w h.length) (contourColLabels u w h.length)
          h.label_ranges_disjoint) = w := by
  have hh := congrArg List.tail
    (contourPattern_graphWalk_map u w h.length h.label_ranges_disjoint)
  simpa only [patternClosedGraphWalk, support_copy, ← List.map_tail, List.tail_cons] using hh

end RandomMatrix
