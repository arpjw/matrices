import RandomMatrix.OrderedContours

/-! Alternating row and column positions in an ordered tree contour. -/

open scoped Classical
namespace RandomMatrix

mutual
  def evenPositions {V : Type*} : List V → List V
    | [] => []
    | x :: xs => x :: oddPositions xs
  def oddPositions {V : Type*} : List V → List V
    | [] => []
    | _ :: xs => evenPositions xs
end

@[simp] theorem evenPositions_cons {V : Type*} (x : V) (xs : List V) :
    evenPositions (x :: xs) = x :: oddPositions xs := by cases xs <;> rfl

@[simp] theorem oddPositions_cons {V : Type*} (x : V) (xs : List V) :
    oddPositions (x :: xs) = evenPositions xs := by cases xs <;> rfl

theorem positions_subset {V : Type*} (xs : List V) :
    evenPositions xs ⊆ xs ∧ oddPositions xs ⊆ xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [evenPositions, oddPositions]
  | singleton x => simp [evenPositions, oddPositions]
  | cons_cons x y xs ih _ =>
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih.1 hv))
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih.2 hv))

theorem positions_length {V : Type*} (xs : List V) :
    (evenPositions xs).length = (xs.length + 1) / 2 ∧
      (oddPositions xs).length = xs.length / 2 := by
  induction xs using List.twoStepInduction with
  | nil => simp [evenPositions, oddPositions]
  | singleton x => simp [evenPositions, oddPositions]
  | cons_cons x y xs ih _ =>
    simp only [evenPositions, oddPositions, List.length_cons, ih.1, ih.2]
    omega

theorem positions_map {V W : Type*} (f : V → W) (xs : List V) :
    evenPositions (xs.map f) = (evenPositions xs).map f ∧
      oddPositions (xs.map f) = (oddPositions xs).map f := by
  induction xs using List.twoStepInduction with
  | nil => simp [evenPositions, oddPositions]
  | singleton x => simp [evenPositions, oddPositions]
  | cons_cons x y xs ih _ => simp [evenPositions, oddPositions, ih]

theorem positions_cover {V : Type*} (xs : List V) (v : V) :
    v ∈ evenPositions xs ∨ v ∈ oddPositions xs ↔ v ∈ xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [evenPositions, oddPositions]
  | singleton x => simp [evenPositions, oddPositions]
  | cons_cons x y xs ih _ =>
    simp only [evenPositions, oddPositions, List.mem_cons]
    aesop

/-- Keeping both parity classes loses no information about the ordered word. -/
theorem positions_injective {V : Type*} (xs ys : List V)
    (he : evenPositions xs = evenPositions ys) (ho : oddPositions xs = oddPositions ys) :
    xs = ys := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp [evenPositions] at he
  | singleton x =>
    cases ys with
    | nil => simp [evenPositions] at he
    | cons y ys =>
      cases ys with
      | nil => simpa [evenPositions, oddPositions] using he
      | cons z ys => simp [evenPositions, oddPositions] at ho
  | cons_cons x y xs ih _ =>
    cases ys with
    | nil => simp [evenPositions] at he
    | cons a ys =>
      cases ys with
      | nil => simp [evenPositions, oddPositions] at ho
      | cons b ys =>
        change x :: evenPositions xs = a :: evenPositions ys at he
        change y :: oddPositions xs = b :: oddPositions ys at ho
        obtain ⟨hx, htailEven⟩ := List.cons.inj he
        obtain ⟨hy, htailOdd⟩ := List.cons.inj ho
        rw [hx, hy, ih ys htailEven htailOdd]

theorem positions_append_even {V : Type*} {xs : List V} (ys : List V)
    {n : ℕ} (hn : xs.length = 2 * n) :
    evenPositions (xs ++ ys) = evenPositions xs ++ evenPositions ys ∧
      oddPositions (xs ++ ys) = oddPositions xs ++ oddPositions ys := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := by simpa using hn
    subst xs
    simp [evenPositions, oddPositions]
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      cases xs with
      | nil => simp at hn; omega
      | cons y xs =>
        have hl : xs.length = 2 * n := by simp only [List.length_cons] at hn; omega
        have ht := ih hl
        simpa only [List.cons_append, evenPositions, oddPositions, List.cons.injEq, true_and]
          using ht

theorem positions_append_odd {V : Type*} {xs : List V} (ys : List V)
    {n : ℕ} (hn : xs.length = 2 * n + 1) :
    evenPositions (xs ++ ys) = evenPositions xs ++ oddPositions ys ∧
      oddPositions (xs ++ ys) = oddPositions xs ++ evenPositions ys := by
  cases xs with
  | nil => simp at hn
  | cons x xs =>
    have hl : xs.length = 2 * n := by simp only [List.length_cons] at hn; omega
    obtain ⟨he, ho⟩ := positions_append_even ys hl
    simp only [List.cons_append, evenPositions_cons, oddPositions_cons, he, ho]
    trivial

mutual
  def treeRows : OrderedTree → ℕ
    | .nil => 1
    | .node _ l r => treeCols l + treeRows r
  def treeCols : OrderedTree → ℕ
    | .nil => 0
    | .node _ l r => treeRows l + treeCols r
end

theorem tree_vertex_counts (t : OrderedTree) : treeRows t + treeCols t = t.numNodes + 1 := by
  induction t with
  | nil => rfl
  | node x l r hl hr => simp only [treeRows, treeCols, Tree.numNodes]; omega

private theorem finset_disjoint_of_list {V : Type*} {a b : List V} (h : List.Disjoint a b) :
    Disjoint a.toFinset b.toFinset := by
  simpa only [Finset.disjoint_left, List.mem_toFinset] using List.disjoint_left.mp h

/-- The color refinement is by row/column depth, with the first child reversing colors. -/
theorem IsOrderedContour.positions {V : Type*} {t : OrderedTree} {u : V} {w : List V}
    (h : IsOrderedContour t u w) :
    List.Disjoint (evenPositions (u :: w)) (oddPositions (u :: w)) ∧
      (evenPositions (u :: w)).toFinset.card = treeRows t ∧
      (oddPositions (u :: w)).toFinset.card = treeCols t := by
  induction h with
  | leaf u => simp [evenPositions, oddPositions, treeRows, treeCols]
  | @graft l r u v a b hl hr hd ihl ihr =>
    have hlen : (v :: a).length = 2 * l.numNodes + 1 := by simp [hl.length]
    obtain ⟨he, ho⟩ := positions_append_odd (u :: b) hlen
    have hdLR : List.Disjoint (oddPositions (v :: a)) (evenPositions (u :: b)) := by
      apply List.disjoint_left.mpr
      intro x hx hy
      exact List.disjoint_left.mp hd ((positions_subset _).2 hx) ((positions_subset _).1 hy)
    have hdRL : List.Disjoint (evenPositions (v :: a)) (oddPositions (u :: b)) := by
      apply List.disjoint_left.mpr
      intro x hx hy
      exact List.disjoint_left.mp hd ((positions_subset _).1 hx) ((positions_subset _).2 hy)
    have hu : u ∈ evenPositions (u :: b) := by simp
    have hrows : evenPositions (u :: ((v :: a) ++ (u :: b))) =
        u :: (oddPositions (v :: a) ++ evenPositions (u :: b)) :=
      (evenPositions_cons _ _).trans (congrArg (List.cons u) ho)
    have hcols : oddPositions (u :: ((v :: a) ++ (u :: b))) =
        evenPositions (v :: a) ++ oddPositions (u :: b) :=
      (oddPositions_cons _ _).trans he
    rw [hrows, hcols]
    refine ⟨?_, ?_, ?_⟩
    · apply List.disjoint_left.mpr
      intro x hx hy
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_append.mp hy with hy | hy
        · exact List.disjoint_left.mp hd ((positions_subset _).1 hy) List.mem_cons_self
        · exact List.disjoint_left.mp ihr.1 hu hy
      · rcases List.mem_append.mp hx with hx | hx <;>
          rcases List.mem_append.mp hy with hy | hy
        · exact List.disjoint_left.mp ihl.1 hy hx
        · exact List.disjoint_left.mp hd ((positions_subset _).2 hx) ((positions_subset _).2 hy)
        · exact List.disjoint_left.mp hd ((positions_subset _).1 hy) ((positions_subset _).1 hx)
        · exact List.disjoint_left.mp ihr.1 hx hy
    · rw [List.toFinset_cons, List.toFinset_append,
        Finset.insert_eq_of_mem (Finset.mem_union_right _ (List.mem_toFinset.mpr hu)),
        Finset.card_union_of_disjoint (finset_disjoint_of_list hdLR), ihl.2.2, ihr.2.1]
      rfl
    · rw [List.toFinset_append,
        Finset.card_union_of_disjoint (finset_disjoint_of_list hdRL), ihl.2.1, ihr.2.2]
      rfl

end RandomMatrix
