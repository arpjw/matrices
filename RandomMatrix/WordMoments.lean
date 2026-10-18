import RandomMatrix.Rademacher
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Exact sign moments of arbitrary coordinate words, including repeated coordinates. -/

open scoped BigOperators
namespace RandomMatrix

/-- Regroup a commutative word product by coordinate multiplicity. -/
theorem word_product_by_count {ι : Type*} [Fintype ι] [DecidableEq ι] [BEq ι] [LawfulBEq ι]
    (w : List ι) (f : ι → ℝ) :
    (w.map f).prod = ∏ i, f i ^ w.count i := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.count_cons, pow_add,
      Finset.prod_mul_distrib]
    simp [beq_iff_eq, mul_comm]

/-- The expectation of a word is exactly one if all coordinate counts are even,
and zero otherwise. This holds at every word length and every finite dimension. -/
theorem average_word {ι : Type*} [Fintype ι] [DecidableEq ι] [BEq ι] [LawfulBEq ι] (w : List ι) :
    average (fun ω : ι → Bool => (w.map (fun i => sign (ω i))).prod) =
      if ∀ i, Even (w.count i) then 1 else 0 := by
  classical
  simp_rw [word_product_by_count]
  rw [average_sign_monomial]
  by_cases h : ∀ i, Even (w.count i)
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The mixed moment of two words is determined by parity of their combined counts. -/
theorem average_word_pair {ι : Type*} [Fintype ι] [DecidableEq ι] [BEq ι] [LawfulBEq ι] (v w : List ι) :
    average (fun ω : ι → Bool =>
      (v.map (fun i => sign (ω i))).prod * (w.map (fun i => sign (ω i))).prod) =
      if ∀ i, Even (v.count i + w.count i) then 1 else 0 := by
  simpa only [List.map_append, List.prod_append, List.count_append] using average_word (v ++ w)

end RandomMatrix
