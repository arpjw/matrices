import RandomMatrix.ContourRoundTrip

/-! The all-order bijection between leading covariance patterns and rooted ordered trees. -/

open scoped Classical
namespace RandomMatrix

/-- A surviving pattern on the leading diagonal, retaining its moment order. -/
structure LeadingPattern where
  order : ℕ
  rows : Setoid (Fin (order + 1))
  cols : Setoid (Fin order)
  survives : PatternSurvives order rows cols
  maximal : blockCount rows + blockCount cols = order + 1

/-- Read the two equality partitions from the canonical tree contour. -/
def treeToLeading (t : OrderedTree) : LeadingPattern where
  order := t.numNodes
  rows := (treePattern t).1
  cols := (treePattern t).2
  survives := (treePattern_leading t).1
  maximal := (treePattern_leading t).2

/-- Every leading pattern has an ordered contour, with no choice of block names. -/
theorem LeadingPattern.exists_contour (q : LeadingPattern) :
    ∃ t, IsOrderedContour t (Sum.inl (Quotient.mk q.rows 0))
      (patternClosedGraphWalk q.rows q.cols q.survives).support.tail := by
  apply acyclic_walk_orderedContour (maximal_pattern_isTree q.rows q.cols q.survives
    q.maximal).IsAcyclic
  intro e
  by_cases he : e ∈ (patternClosedGraphWalk q.rows q.cols q.survives).edges
  · have hh := maximal_patternClosedGraphWalk_edges_twice q.rows q.cols q.survives q.maximal e he
    simp only [List.count_eq_countP, Bool.beq_eq_decide_eq] at hh ⊢
    omega
  · have hh := List.count_eq_zero.mpr he
    simp only [List.count_eq_countP, Bool.beq_eq_decide_eq] at hh ⊢
    omega

/-- Reconstruct the unique rooted ordered shape from the original entry order. -/
noncomputable def leadingToTree (q : LeadingPattern) : OrderedTree :=
  q.exists_contour.choose

theorem leadingToTree_contour (q : LeadingPattern) :
    IsOrderedContour (leadingToTree q) (Sum.inl (Quotient.mk q.rows 0))
      (patternClosedGraphWalk q.rows q.cols q.survives).support.tail :=
  q.exists_contour.choose_spec

theorem leadingToTree_numNodes (q : LeadingPattern) :
    (leadingToTree q).numNodes = q.order := by
  have h := (leadingToTree_contour q).length
  rw [patternClosedGraphWalk_tail_length] at h
  omega

/-- The reconstruction of a canonical contour has the original ordered shape. -/
theorem leadingToTree_treeToLeading (t : OrderedTree) :
    leadingToTree (treeToLeading t) = t := by
  let hc := treeContour_valid t
  let emb := labelSumEmbedding (contourRowLabels (treeRoot t) (treeContour t) hc.length)
    (contourColLabels (treeRoot t) (treeContour t) hc.length) hc.label_ranges_disjoint
  have hm := (leadingToTree_contour (treeToLeading t)).map emb emb.injective
  have hr : emb (Sum.inl (Quotient.mk (treeToLeading t).rows 0)) = treeRoot t := by
    change contourRowLabels (treeRoot t) (treeContour t) hc.length 0 = treeRoot t
    exact contourRowLabels_zero _ _ _
  have hw := hc.graphWalk_map
  change (patternClosedGraphWalk (treeToLeading t).rows (treeToLeading t).cols
    (treeToLeading t).survives).support.tail.map emb = treeContour t at hw
  rw [hr, hw] at hm
  exact hm.unique hc rfl rfl

/-- Every original leading pattern is the canonical contour pattern of some ordered tree. -/
theorem treeToLeading_surjective : Function.Surjective treeToLeading := by
  rintro ⟨k, r, c, hs, hmax⟩
  obtain ⟨t, ht⟩ := (LeadingPattern.mk k r c hs hmax).exists_contour
  change IsOrderedContour t (Sum.inl (Quotient.mk r 0))
    (patternClosedGraphWalk r c hs).support.tail at ht
  have hn : t.numNodes = k := by
    have hl := ht.length
    rw [patternClosedGraphWalk_tail_length] at hl
    omega
  subst k
  obtain ⟨f, hf, hr, hw⟩ := ht.representation
  have hp := contourPattern_map (treeRoot t) (treeContour t) (treeContour_length t) f hf
    (by rw [List.length_map, treeContour_length])
  simp only [hr, hw] at hp
  have hpat : treePattern t = (r, c) := by
    rw [patternClosedGraphWalk_pattern] at hp
    exact hp.symm
  refine ⟨t, ?_⟩
  have hrows := congrArg Prod.fst hpat
  have hcols := congrArg Prod.snd hpat
  unfold treeToLeading
  cases hrows
  cases hcols
  rfl

/-- Reading the reconstructed tree returns the original pair of equality partitions. -/
theorem treeToLeading_leadingToTree (q : LeadingPattern) :
    treeToLeading (leadingToTree q) = q := by
  obtain ⟨t, rfl⟩ := treeToLeading_surjective q
  rw [leadingToTree_treeToLeading]

/-- The general leading-pattern / rooted-ordered-tree equivalence. -/
noncomputable def orderedTreeLeadingEquiv : OrderedTree ≃ LeadingPattern where
  toFun := treeToLeading
  invFun := leadingToTree
  left_inv := leadingToTree_treeToLeading
  right_inv := treeToLeading_leadingToTree

theorem orderedTreeLeadingEquiv_counts (t : OrderedTree) :
    (orderedTreeLeadingEquiv t).order = t.numNodes ∧
      blockCount (orderedTreeLeadingEquiv t).rows = treeRows t ∧
      blockCount (orderedTreeLeadingEquiv t).cols = treeCols t :=
  ⟨rfl, treePattern_block_counts t⟩

end RandomMatrix
