import RandomMatrix.PatternBoundary
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The connected bipartite graph on the row and column blocks of a pattern. -/

open scoped Classical
namespace RandomMatrix

/-- An entry joins a row vertex to a column vertex. The two vertex types stay disjoint. -/
def bipartiteEntryGraph {R C : Type*} (E : Set (R × C)) : SimpleGraph (R ⊕ C) where
  Adj
    | .inl r, .inr c => (r, c) ∈ E
    | .inr c, .inl r => (r, c) ∈ E
    | _, _ => False
  symm := by rintro (r | c) (r' | c') <;> exact id
  loopless := ⟨by rintro (r | c) <;> exact id⟩

theorem bipartiteEntryGraph_isBipartite {R C : Type*} (E : Set (R × C)) :
    (bipartiteEntryGraph E).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1)) ?_⟩
  rintro (r | c) (r' | c') h
  · exact False.elim h
  · exact Fin.zero_ne_one
  · exact Fin.zero_ne_one.symm
  · exact False.elim h

/-- Distinct matrix entries are exactly the undirected edges of the bipartite graph. -/
noncomputable def entryGraphEdgeEquiv {R C : Type*} (E : Set (R × C)) :
    E ≃ (bipartiteEntryGraph E).edgeSet :=
  Equiv.ofBijective
    (fun e => ⟨s(Sum.inl e.1.1, Sum.inr e.1.2), e.2⟩) (by
      constructor
      · intro e f h
        apply Subtype.ext
        have he := congrArg Subtype.val h
        simpa [Sym2.eq_iff, Prod.ext_iff] using he
      · rintro ⟨e, he⟩
        revert he
        refine Sym2.inductionOn e ?_
        rintro (r | c) (r' | c') he
        · exact False.elim he
        · exact ⟨⟨(r, c'), he⟩, rfl⟩
        · refine ⟨⟨(r', c), he⟩, Subtype.ext ?_⟩
          exact Sym2.eq_swap
        · exact False.elim he)

theorem entryGraph_edge_card {R C : Type*} (E : Finset (R × C)) :
    Nat.card (bipartiteEntryGraph (E : Set (R × C))).edgeSet = E.card := by
  rw [← Nat.card_congr (entryGraphEdgeEquiv (E : Set (R × C)))]
  simp [Nat.card_eq_fintype_card]

/-- The entry word with labels given by the actual quotient blocks. -/
def patternWord {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) :
    List (Quotient r × Quotient c) :=
  (positionWord k).map (fun e => (Quotient.mk r e.1, Quotient.mk c e.2))

noncomputable def patternEdges {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) :
    Finset (Quotient r × Quotient c) := (patternWord r c).toFinset

/-- Vertices are partition blocks, not numerical choices of their representatives. -/
noncomputable def patternGraph {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) :
    SimpleGraph (Quotient r ⊕ Quotient c) :=
  bipartiteEntryGraph (patternEdges r c : Set (Quotient r × Quotient c))

theorem patternGraph_isBipartite {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) :
    (patternGraph r c).IsBipartite :=
  bipartiteEntryGraph_isBipartite _

theorem patternGraph_vertex_card {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) :
    Nat.card (Quotient r ⊕ Quotient c) = blockCount r + blockCount c :=
  Nat.card_sum

theorem patternGraph_edge_card {k : ℕ} (r : Setoid (Fin (k + 1))) (c : Setoid (Fin k)) :
    Nat.card (patternGraph r c).edgeSet = (patternEdges r c).card :=
  entryGraph_edge_card _

/-- Each column position is incident to the row immediately before it. -/
theorem positionWord_left_mem {k : ℕ} (j : Fin k) :
    (j.castSucc, j) ∈ positionWord k := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [positionWord]
    · simp only [positionWord, List.mem_cons, List.mem_map]
      exact Or.inr (Or.inr ⟨(j.castSucc, j), ih j, rfl⟩)

/-- Each column position is incident to the row immediately after it. -/
theorem positionWord_right_mem {k : ℕ} (j : Fin k) :
    (j.succ, j) ∈ positionWord k := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [positionWord]
    · simp only [positionWord, List.mem_cons, List.mem_map]
      exact Or.inr (Or.inr ⟨(j.succ, j), ih j, rfl⟩)

theorem patternGraph_adj_of_position {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) (e : Fin (k + 1) × Fin k) (he : e ∈ positionWord k) :
    (patternGraph r c).Adj (.inl (Quotient.mk r e.1)) (.inr (Quotient.mk c e.2)) := by
  change (Quotient.mk r e.1, Quotient.mk c e.2) ∈ (patternWord r c).toFinset
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- All block vertices are reached by the alternating position walk, even without parity or closure. -/
theorem patternGraph_connected {k : ℕ} (r : Setoid (Fin (k + 1)))
    (c : Setoid (Fin k)) : (patternGraph r c).Connected := by
  let root : Quotient r ⊕ Quotient c := .inl (Quotient.mk r 0)
  have hr (j : Fin (k + 1)) :
      (patternGraph r c).Reachable root (.inl (Quotient.mk r j)) := by
    induction j using Fin.induction with
    | zero => exact .refl _
    | succ j ih =>
      exact ih.trans ((patternGraph_adj_of_position r c _ (positionWord_left_mem j)).reachable.trans
        (patternGraph_adj_of_position r c _ (positionWord_right_mem j)).symm.reachable)
  have hall (v : Quotient r ⊕ Quotient c) : (patternGraph r c).Reachable root v := by
    rcases v with v | v
    · induction v using Quotient.inductionOn with | h j => exact hr j
    · induction v using Quotient.inductionOn with
      | h j =>
        exact (hr j.castSucc).trans
          (patternGraph_adj_of_position r c _ (positionWord_left_mem j)).reachable
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨root, hall⟩

end RandomMatrix
