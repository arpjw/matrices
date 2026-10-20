import RandomMatrix.OrderedContours

/-! Closure and edge parity of rooted ordered contours. -/

open scoped Classical
namespace RandomMatrix

def contourEdges {V : Type*} : V → List V → List (Sym2 V)
  | _, [] => []
  | u, v :: w => s(u, v) :: contourEdges v w

theorem contourEdges_map {V W : Type*} (f : V → W) (u : V) (w : List V) :
    contourEdges (f u) (w.map f) = (contourEdges u w).map (Sym2.map f) := by
  induction w generalizing u with
  | nil => rfl
  | cons v w ih => simp [contourEdges, ih]

/-- A contour returns to its root before any subsequent walk begins. -/
theorem IsOrderedContour.edges_append {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) (z : List V) :
    contourEdges u (w ++ z) = contourEdges u w ++ contourEdges u z := by
  induction h generalizing z with
  | leaf => rfl
  | @graft l r u v a b hl hr hd ihl ihr =>
    simp only [List.append_assoc, List.cons_append, contourEdges, ihl, ihr]

theorem IsOrderedContour.last {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) :
    (u :: w).getLast? = some u := by
  induction h with
  | leaf => rfl
  | graft hl hr hd ihl ihr =>
    rw [← List.cons_append, List.getLast?_append, ihr]
    rfl

/-- Every undirected entry has even multiplicity in an ordered tree contour. -/
theorem IsOrderedContour.edges_even {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) (e : Sym2 V) :
    Even ((contourEdges u w).count e) := by
  induction h with
  | leaf => exact ⟨0, rfl⟩
  | @graft l r u v a b hl hr hd ihl ihr =>
    have hs : s(v, u) = s(u, v) := Sym2.eq_swap
    obtain ⟨m, hm⟩ := ihl
    obtain ⟨n, hn⟩ := ihr
    simp only [List.cons_append, contourEdges, hl.edges_append, contourEdges,
      List.count_cons, List.count_append, hs]
    refine ⟨m + n + (if s(u, v) == e then 1 else 0), ?_⟩
    split <;> omega

end RandomMatrix
