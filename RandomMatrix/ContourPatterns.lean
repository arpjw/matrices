import RandomMatrix.ContourLabelings
import RandomMatrix.CanonicalContours

/-! Turning rooted ordered contours into the original two-partition moment patterns. -/

open scoped Classical
namespace RandomMatrix

def kernelLabelEmbedding {A V : Type*} (f : A → V) : Quotient (Setoid.ker f) ↪ V :=
  kernelFiberEquiv (Setoid.ker f) ⟨f, rfl⟩

@[simp] theorem kernelLabelEmbedding_mk {A V : Type*} (f : A → V) (a : A) :
    kernelLabelEmbedding f (Quotient.mk _ a) = f a := rfl

theorem kernelLabelEmbedding_mem_range {A V : Type*} (f : A → V)
    (x : Quotient (Setoid.ker f)) : kernelLabelEmbedding f x ∈ Set.range f := by
  induction x using Quotient.inductionOn with
  | h a => exact ⟨a, rfl⟩

def labelSumEmbedding {A B V : Type*} (f : A → V) (g : B → V)
    (hd : Disjoint (Set.range f) (Set.range g)) :
    (Quotient (Setoid.ker f) ⊕ Quotient (Setoid.ker g)) ↪ V where
  toFun := Sum.elim (kernelLabelEmbedding f) (kernelLabelEmbedding g)
  inj' := by
    rintro (x | x) (y | y) he
    · exact congrArg Sum.inl ((kernelLabelEmbedding f).injective he)
    · change kernelLabelEmbedding f x = kernelLabelEmbedding g y at he
      exact False.elim (Set.disjoint_left.mp hd (kernelLabelEmbedding_mem_range f x)
        (he.symm ▸ kernelLabelEmbedding_mem_range g y))
    · change kernelLabelEmbedding g x = kernelLabelEmbedding f y at he
      exact False.elim (Set.disjoint_left.mp hd (kernelLabelEmbedding_mem_range f y)
        (he ▸ kernelLabelEmbedding_mem_range g x))
    · exact congrArg Sum.inr ((kernelLabelEmbedding g).injective he)

def positionEntryEmbedding {A B V : Type*} (f : A → V) (g : B → V)
    (hd : Disjoint (Set.range f) (Set.range g)) :
    (Quotient (Setoid.ker f) × Quotient (Setoid.ker g)) ↪ Sym2 V where
  toFun e := s(labelSumEmbedding f g hd (.inl e.1), labelSumEmbedding f g hd (.inr e.2))
  inj' := by
    intro a b he
    rcases Sym2.eq_iff.mp he with he | he
    · exact Prod.ext (Sum.inl.inj ((labelSumEmbedding f g hd).injective he.1))
        (Sum.inr.inj ((labelSumEmbedding f g hd).injective he.2))
    · have hh := (labelSumEmbedding f g hd).injective he.1
      cases hh

@[simp] theorem positionEntryEmbedding_mk {A B V : Type*} (f : A → V) (g : B → V)
    (hd : Disjoint (Set.range f) (Set.range g)) (a : A) (b : B) :
    positionEntryEmbedding f g hd (Quotient.mk _ a, Quotient.mk _ b) = s(f a, g b) := rfl

def contourPattern {V : Type*} {k : ℕ} (u : V) (w : List V) (h : w.length = 2 * k) :
    Setoid (Fin (k + 1)) × Setoid (Fin k) :=
  (Setoid.ker (contourRowLabels u w h), Setoid.ker (contourColLabels u w h))

theorem contourPattern_map {V W : Type*} {k : ℕ} (u : V) (w : List V)
    (h : w.length = 2 * k) (f : V → W) (hf : Function.Injective f)
    (hm : (w.map f).length = 2 * k) :
    contourPattern (f u) (w.map f) hm = contourPattern u w h := by
  apply Prod.ext
  · apply Setoid.ext
    intro a b
    simp only [contourPattern, Setoid.ker_def, contourRowLabels_map u w h f hm,
      Function.comp_apply, hf.eq_iff]
  · apply Setoid.ext
    intro a b
    simp only [contourPattern, Setoid.ker_def, contourColLabels_map u w h f hm,
      Function.comp_apply, hf.eq_iff]

theorem IsOrderedContour.label_ranges_disjoint {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) :
    Disjoint (Set.range (contourRowLabels u w h.length))
      (Set.range (contourColLabels u w h.length)) := by
  unfold contourRowLabels contourColLabels
  rw [listLabels_range, listLabels_range]
  simpa only [Set.disjoint_left, Finset.mem_coe, List.mem_toFinset] using
    List.disjoint_left.mp h.positions.1

/-- The contour's two equality partitions have exactly the tree's two color counts. -/
theorem IsOrderedContour.block_counts {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) :
    blockCount (contourPattern u w h.length).1 = treeRows t ∧
      blockCount (contourPattern u w h.length).2 = treeCols t := by
  simp only [contourPattern, contourRowLabels, contourColLabels, listLabels_blockCount]
  exact h.positions.2

/-- Every rooted ordered tree contour gives a surviving maximal moment pattern. -/
theorem IsOrderedContour.pattern_leading {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (h : IsOrderedContour t u w) :
    PatternSurvives t.numNodes (contourPattern u w h.length).1
      (contourPattern u w h.length).2 ∧
    blockCount (contourPattern u w h.length).1 +
      blockCount (contourPattern u w h.length).2 = t.numNodes + 1 := by
  refine ⟨?_, ?_⟩
  · apply (patternSurvives_iff_closed_even _ _).mpr
    refine ⟨Quotient.sound h.rowLabels_closed, ?_⟩
    let emb := positionEntryEmbedding (contourRowLabels u w h.length)
      (contourColLabels u w h.length) h.label_ranges_disjoint
    have he : (patternWord (contourPattern u w h.length).1
        (contourPattern u w h.length).2).map emb = contourEdges u w := by
      simpa only [patternWord, contourPattern, List.map_map, Function.comp_def,
        emb, positionEntryEmbedding_mk] using contour_position_edges u w h.length
    intro e
    have hh := h.edges_even (emb e)
    rw [← he, List.count_map_of_injective _ emb emb.injective] at hh
    exact hh
  · rw [h.block_counts.1, h.block_counts.2, tree_vertex_counts]

def treePattern (t : OrderedTree) :
    Setoid (Fin (t.numNodes + 1)) × Setoid (Fin t.numNodes) :=
  contourPattern (treeRoot t) (treeContour t) (treeContour_length t)

theorem treePattern_leading (t : OrderedTree) :
    PatternSurvives t.numNodes (treePattern t).1 (treePattern t).2 ∧
      blockCount (treePattern t).1 + blockCount (treePattern t).2 = t.numNodes + 1 :=
  (treeContour_valid t).pattern_leading

theorem treePattern_block_counts (t : OrderedTree) :
    blockCount (treePattern t).1 = treeRows t ∧ blockCount (treePattern t).2 = treeCols t :=
  (treeContour_valid t).block_counts

end RandomMatrix
