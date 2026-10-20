import RandomMatrix.TreeWalkSplit
import Mathlib.Data.Tree.Basic

/-! Rooted ordered tree contours and their unique reconstruction from doubled tree walks. -/

open scoped Classical
open SimpleGraph SimpleGraph.Walk
namespace RandomMatrix

/-- `Tree Unit` is read as first child / remaining children, with `nil` the single root. -/
abbrev OrderedTree := Tree Unit

/-- A labeled contour: descend to the first child, traverse it, return, then traverse the rest.
The disjointness condition says that different tree vertices have different labels. -/
inductive IsOrderedContour {V : Type*} : OrderedTree → V → List V → Prop
  | leaf (u : V) : IsOrderedContour .nil u []
  | graft {l r : OrderedTree} {u v : V} {a b : List V}
      (left : IsOrderedContour l v a) (right : IsOrderedContour r u b)
      (disjoint : List.Disjoint (v :: a) (u :: b)) :
      IsOrderedContour (.node () l r) u ((v :: a) ++ (u :: b))

theorem IsOrderedContour.length {V : Type*} {t : OrderedTree} {u : V} {w : List V}
    (h : IsOrderedContour t u w) : w.length = 2 * t.numNodes := by
  induction h with
  | leaf => rfl
  | graft ha hb hd iha ihb =>
    simp only [List.length_append, List.length_cons, Tree.numNodes]
    omega

private theorem first_marker_split {V : Type*} (u : V) {a b c d : List V}
    (ha : u ∉ a) (hc : u ∉ c) (he : a ++ u :: b = c ++ u :: d) :
    a = c ∧ b = d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => simpa using he
    | cons v c =>
      have hv : u = v := (List.cons.inj he).1
      exact False.elim (hc (hv ▸ List.mem_cons_self))
  | cons v a ih =>
    cases c with
    | nil =>
      have hv : v = u := (List.cons.inj he).1
      exact False.elim (ha (hv ▸ List.mem_cons_self))
    | cons x c =>
      obtain ⟨rfl, hh⟩ := List.cons.inj he
      have ht := ih (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hc (List.mem_cons_of_mem _ h)) hh
      exact ⟨congrArg (List.cons v) ht.1, ht.2⟩

/-- A contour determines its rooted ordered tree, including child order. -/
theorem IsOrderedContour.unique {V : Type*} {t : OrderedTree} {u : V} {w : List V}
    (h : IsOrderedContour t u w) :
    ∀ {s : OrderedTree} {v : V} {z : List V}, IsOrderedContour s v z →
      u = v → w = z → t = s := by
  induction h with
  | leaf u =>
    intro s v z hs huv hw
    cases hs with
    | leaf => rfl
    | graft => simp at hw
  | @graft l r u v a b hl hr hd ihl ihr =>
    intro s x z hs hux hw
    subst x
    cases hs with
    | leaf => simp at hw
    | @graft l' r' _ v' a' b' hl' hr' hd' =>
      have hn : u ∉ v :: a := fun hu =>
        (List.disjoint_left.mp hd hu (List.mem_cons_self))
      have hn' : u ∉ v' :: a' := fun hu =>
        (List.disjoint_left.mp hd' hu (List.mem_cons_self))
      obtain ⟨hc, hb⟩ := first_marker_split u hn hn' hw
      have hv := List.cons.inj hc
      rw [ihl hl' hv.1 hv.2, ihr hr' rfl hb]

/-- Injective changes of vertex labels preserve the tree and its ordered contour. -/
theorem IsOrderedContour.map {V W : Type*} {t : OrderedTree} {u : V} {w : List V}
    (h : IsOrderedContour t u w) (f : V → W) (hf : Function.Injective f) :
    IsOrderedContour t (f u) (w.map f) := by
  induction h with
  | leaf => exact .leaf _
  | graft ha hb hd iha ihb =>
    simpa only [List.map_append, List.map_cons] using
      IsOrderedContour.graft iha ihb (hd.map hf)

/-- Every closed walk in an acyclic graph using an edge at most twice is an ordered contour. -/
theorem acyclic_walk_orderedContour {V : Type*} {G : SimpleGraph V} (hg : G.IsAcyclic)
    {u : V} (p : G.Walk u u) (hc : ∀ e, p.edges.count e ≤ 2) :
    ∃ t : OrderedTree, IsOrderedContour t u p.support.tail := by
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    cases p with
    | nil => exact ⟨.nil, .leaf _⟩
    | @cons u v _ h q =>
      obtain ⟨a, b, hq, hd, ha, hb⟩ := tree_walk_first_child_split hg h q hc
      have hlen : a.length + b.length + 2 = n := by
        simp only [hq, length_cons, length_append] at hn
        omega
      obtain ⟨l, hl⟩ := ih a.length (by omega) a ha rfl
      obtain ⟨r, hr⟩ := ih b.length (by omega) b hb rfl
      refine ⟨.node () l r, ?_⟩
      have hdis : List.Disjoint (v :: a.support.tail) (u :: b.support.tail) := by
        simpa only [← support_eq_cons] using hd
      have hcont := IsOrderedContour.graft hl hr hdis
      simpa only [support_cons, List.tail_cons, hq, support_append, support_cons,
        List.tail_cons, ← support_eq_cons] using hcont

end RandomMatrix
