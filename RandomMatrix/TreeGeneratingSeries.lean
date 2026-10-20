import RandomMatrix.TreeCoefficients
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination

/-! The two color-counting series and their exact quadratic equation. -/

open scoped BigOperators Classical
namespace RandomMatrix

noncomputable def rowTreePoly (n : ℕ) : Polynomial ℚ :=
  ∑ t ∈ Tree.treesOfNumNodesEq n, Polynomial.X ^ treeRows t

noncomputable def colTreePoly (n : ℕ) : Polynomial ℚ :=
  ∑ t ∈ Tree.treesOfNumNodesEq n, Polynomial.X ^ treeCols t

private theorem sum_trees_succ {R : Type*} [AddCommMonoid R] (f : OrderedTree → R) (n : ℕ) :
    ∑ t ∈ Tree.treesOfNumNodesEq (n + 1), f t =
      ∑ ij ∈ Finset.antidiagonal n, ∑ l ∈ Tree.treesOfNumNodesEq ij.1,
        ∑ r ∈ Tree.treesOfNumNodesEq ij.2, f (.node () l r) := by
  rw [Tree.treesOfNumNodesEq_succ, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro ij hij
    simp only [Tree.pairwiseNode, Finset.sum_map, Finset.sum_product]
    rfl
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, Finset.disjoint_left]
    aesop

@[simp] theorem rowTreePoly_zero : rowTreePoly 0 = Polynomial.X := by
  simp [rowTreePoly, treeRows]

@[simp] theorem colTreePoly_zero : colTreePoly 0 = 1 := by
  simp [colTreePoly, treeCols]

theorem rowTreePoly_succ (n : ℕ) :
    rowTreePoly (n + 1) = ∑ ij ∈ Finset.antidiagonal n, colTreePoly ij.1 * rowTreePoly ij.2 := by
  rw [rowTreePoly, sum_trees_succ]
  simp only [treeRows, pow_add, colTreePoly, rowTreePoly, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  exact Finset.sum_comm

theorem colTreePoly_succ (n : ℕ) :
    colTreePoly (n + 1) = ∑ ij ∈ Finset.antidiagonal n, rowTreePoly ij.1 * colTreePoly ij.2 := by
  rw [colTreePoly, sum_trees_succ]
  simp only [treeCols, pow_add, colTreePoly, rowTreePoly, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  exact Finset.sum_comm

noncomputable def rowTreeSeries : PowerSeries (Polynomial ℚ) := PowerSeries.mk rowTreePoly
noncomputable def colTreeSeries : PowerSeries (Polynomial ℚ) := PowerSeries.mk colTreePoly

@[simp] theorem coeff_rowTreeSeries (n : ℕ) : PowerSeries.coeff n rowTreeSeries = rowTreePoly n :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_colTreeSeries (n : ℕ) : PowerSeries.coeff n colTreeSeries = colTreePoly n :=
  PowerSeries.coeff_mk _ _

theorem rowTreeSeries_eq : rowTreeSeries = PowerSeries.C Polynomial.X +
    PowerSeries.X * (colTreeSeries * rowTreeSeries) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, rowTreeSeries, PowerSeries.constantCoeff_mk]
  | succ n =>
    rw [map_add, PowerSeries.coeff_succ_X_mul]
    simp only [PowerSeries.coeff_succ_C, zero_add,
      coeff_rowTreeSeries, PowerSeries.coeff_mul, coeff_colTreeSeries, rowTreePoly_succ]

theorem colTreeSeries_eq : colTreeSeries = 1 +
    PowerSeries.X * (rowTreeSeries * colTreeSeries) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, colTreeSeries, PowerSeries.constantCoeff_mk]
  | succ n =>
    rw [map_add, PowerSeries.coeff_succ_X_mul]
    simp only [PowerSeries.coeff_one, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, zero_add,
      coeff_colTreeSeries, PowerSeries.coeff_mul, coeff_rowTreeSeries, colTreePoly_succ]

theorem rowTreeSeries_sub_colTreeSeries :
    rowTreeSeries - colTreeSeries = PowerSeries.C Polynomial.X - 1 := by
  linear_combination rowTreeSeries_eq - colTreeSeries_eq

/-- Elimination of the other root color gives the Narayana quadratic equation. -/
theorem colTreeSeries_quadratic :
    colTreeSeries = 1 + PowerSeries.X * colTreeSeries *
      (colTreeSeries + PowerSeries.C Polynomial.X - 1) := by
  linear_combination colTreeSeries_eq + PowerSeries.X * colTreeSeries *
    rowTreeSeries_sub_colTreeSeries

end RandomMatrix
