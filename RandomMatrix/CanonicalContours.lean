import RandomMatrix.OrderedContours

/-! Canonical distinct vertex labels for each rooted ordered tree. -/

open scoped Classical
namespace RandomMatrix

def TreeVertex : OrderedTree → Type
  | .nil => Unit
  | .node _ l r => TreeVertex l ⊕ TreeVertex r

def treeRoot : (t : OrderedTree) → TreeVertex t
  | .nil => ()
  | .node _ _ r => .inr (treeRoot r)

def treeContour : (t : OrderedTree) → List (TreeVertex t)
  | .nil => []
  | .node _ l r =>
    ((treeRoot l :: treeContour l).map Sum.inl) ++
      ((treeRoot r :: treeContour r).map Sum.inr)

theorem treeContour_valid (t : OrderedTree) :
    IsOrderedContour t (treeRoot t) (treeContour t) := by
  induction t with
  | nil => exact .leaf _
  | node x l r hl hr =>
    cases x
    have hd : List.Disjoint ((treeRoot l :: treeContour l).map
        (Sum.inl : TreeVertex l → TreeVertex l ⊕ TreeVertex r))
        ((treeRoot r :: treeContour r).map Sum.inr) := by
      simp [List.disjoint_left]
    simpa only [treeRoot, treeContour, List.map_cons] using
      IsOrderedContour.graft (hl.map Sum.inl Sum.inl_injective)
        (hr.map Sum.inr Sum.inr_injective) hd

theorem treeVertex_mem_contour (t : OrderedTree) (v : TreeVertex t) :
    v ∈ treeRoot t :: treeContour t := by
  induction t with
  | nil => cases v; simp [treeRoot]
  | node x l r hl hr =>
    cases v with
    | inl v =>
      exact List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.mpr ⟨v, hl v, rfl⟩))
    | inr v =>
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_map.mpr ⟨v, hr v, rfl⟩))

theorem treeContour_length (t : OrderedTree) : (treeContour t).length = 2 * t.numNodes :=
  (treeContour_valid t).length

/-- A labeled contour is an injective relabeling of the canonical contour of its shape. -/
theorem IsOrderedContour.representation {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) :
    ∃ f : TreeVertex t → V, Function.Injective f ∧
      f (treeRoot t) = u ∧ (treeContour t).map f = w := by
  induction h with
  | leaf u =>
    exact ⟨fun _ => u, fun a b _ => by cases a; cases b; rfl, rfl, rfl⟩
  | @graft l r u v a b hl hr hd ihl ihr =>
    obtain ⟨f, hf, hfr, hfw⟩ := ihl
    obtain ⟨g, hg, hgr, hgw⟩ := ihr
    have hfm (x : TreeVertex l) : f x ∈ v :: a := by
      rw [← hfr, ← hfw, ← List.map_cons]
      exact List.mem_map.mpr ⟨x, treeVertex_mem_contour l x, rfl⟩
    have hgm (x : TreeVertex r) : g x ∈ u :: b := by
      rw [← hgr, ← hgw, ← List.map_cons]
      exact List.mem_map.mpr ⟨x, treeVertex_mem_contour r x, rfl⟩
    refine ⟨Sum.elim f g, ?_, hgr, ?_⟩
    · rintro (x | x) (y | y) he
      · exact congrArg Sum.inl (hf he)
      · change f x = g y at he
        exact False.elim (List.disjoint_left.mp hd (hfm x) (he.symm ▸ hgm y))
      · change g x = f y at he
        exact False.elim (List.disjoint_left.mp hd (hfm y) (he ▸ hgm x))
      · exact congrArg Sum.inr (hg he)
    · simp [treeContour, List.map_append, List.map_map, Function.comp_def,
        hfr, hfw, hgr, hgw]

end RandomMatrix
