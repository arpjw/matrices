import RandomMatrix.PatternContour

/-! Splitting a doubled tree walk into its first child excursion and the remaining excursions. -/

open scoped Classical
open SimpleGraph SimpleGraph.Walk
namespace RandomMatrix

/-- Opposite sides of a bridge have disjoint edge-avoiding walk supports. -/
theorem bridge_walk_support_disjoint {V : Type*} {G : SimpleGraph V} {u v : V}
    (hb : G.IsBridge s(u, v)) (a : G.Walk v v) (b : G.Walk u u)
    (ha : s(u, v) ∉ a.edges) (hc : s(u, v) ∉ b.edges) :
    List.Disjoint a.support b.support := by
  apply List.disjoint_left.mpr
  intro w hwa hwb
  obtain ⟨a₁, a₂, heqa⟩ := mem_support_iff_exists_append.mp hwa
  obtain ⟨b₁, b₂, heqb⟩ := mem_support_iff_exists_append.mp hwb
  have hmust := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hb).2
    (b₁.append a₁.reverse)
  simp only [edges_append, edges_reverse, List.mem_append, List.mem_reverse] at hmust
  rcases hmust with he | he
  · apply hc
    rw [heqb, edges_append]
    exact List.mem_append_left _ he
  · apply ha
    rw [heqa, edges_append]
    exact List.mem_append_left _ he

/-- A closed acyclic walk with at most two visits per edge has a disjoint first-child split. -/
theorem tree_walk_first_child_split {V : Type*} {G : SimpleGraph V} {u v : V}
    (hg : G.IsAcyclic) (h : G.Adj u v) (q : G.Walk v u)
    (hc : ∀ e, (Walk.cons h q).edges.count e ≤ 2) :
    ∃ (a : G.Walk v v) (b : G.Walk u u),
      q = a.append (Walk.cons h.symm b) ∧ List.Disjoint a.support b.support ∧
      (∀ e, a.edges.count e ≤ 2) ∧ (∀ e, b.edges.count e ≤ 2) := by
  have hb := isAcyclic_iff_forall_adj_isBridge.mp hg h
  have hb' := isAcyclic_iff_forall_adj_isBridge.mp hg h.symm
  have hback := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hb').2 q
  have hs : s(v, u) = s(u, v) := Sym2.eq_swap
  rcases (isSubwalk_toWalk_iff_mem_edges h.symm).mpr hback with hsub | hsub
  · obtain ⟨a, b, hq⟩ := hsub
    have hq' : q = a.append (Walk.cons h.symm b) := by
      simpa [← Walk.append_assoc, SimpleGraph.Adj.toWalk] using hq
    have he := hc s(u, v)
    rw [hq'] at he
    simp only [edges_cons, edges_append, List.count_append, List.count_cons_self, hs] at he
    have ha : s(u, v) ∉ a.edges := List.count_eq_zero.mp (by omega)
    have hb0 : s(u, v) ∉ b.edges := List.count_eq_zero.mp (by omega)
    refine ⟨a, b, hq', bridge_walk_support_disjoint hb a b ha hb0, ?_, ?_⟩
    · intro e
      have hh := hc e
      rw [hq'] at hh
      simp only [edges_cons, edges_append, List.count_append, List.count_cons] at hh
      omega
    · intro e
      have hh := hc e
      rw [hq'] at hh
      simp only [edges_cons, edges_append, List.count_append, List.count_cons] at hh
      omega
  · obtain ⟨a, b, hq⟩ := hsub
    have he := hc s(u, v)
    rw [hq] at he
    simp only [edges_cons, edges_append, List.count_append, List.count_cons_self,
      SimpleGraph.Adj.toWalk, edges_nil, List.count_nil] at he
    have hma := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hb').2 a
    rw [hs] at hma
    have hpos := List.count_pos_iff.mpr hma
    omega

end RandomMatrix
