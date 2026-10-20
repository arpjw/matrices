import RandomMatrix.MomentPolynomials
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! The real Narayana moment polynomials inherit the proved tree recurrence. -/

open scoped BigOperators Classical
namespace RandomMatrix

theorem colTreePoly_degree_le (k : ℕ) : (colTreePoly k).natDegree ≤ k := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  rw [colTreePoly_coeff_narayana]
  cases k with
  | zero => cases r <;> simp_all [narayanaQ]
  | succ k =>
    cases r with
    | zero => omega
    | succ r => simp [narayanaQ, binomQ, Nat.choose_eq_zero_of_lt hr]

/-- At positive order the tree polynomial is gamma times the MP moment. -/
theorem colTreePoly_eval_mpMoment (k : ℕ) (hk : 0 < k) (γ : ℝ) :
    (colTreePoly k).eval₂ (Rat.castHom ℝ) γ = γ * mpMoment k γ := by
  rw [Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ)
    (lt_of_le_of_lt (colTreePoly_degree_le k) (Nat.lt_succ_self k))]
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, colTreePoly_coeff_narayana, narayanaQ_zero_right k hk,
    map_zero, zero_mul, zero_add, Fin.val_succ]
  rw [mpMoment, if_neg hk.ne', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [narayanaQ_pos k j.val hk]
  simp [binomQ, pow_succ]
  ring

/-- The three-term recurrence, in the convention P_0=1 and P_1=1. -/
theorem mpMoment_recurrence (k : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    (k + 4 : ℝ) * mpMoment (k + 3) γ =
      (2 * k + 5 : ℝ) * (1 + γ) * mpMoment (k + 2) γ -
        (k + 1 : ℝ) * (γ - 1) ^ 2 * mpMoment (k + 1) γ := by
  have h := congrArg (fun p : Polynomial ℚ => p.eval₂ (Rat.castHom ℝ) γ)
    (colTreePoly_recurrence (k + 1))
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_natCast,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one, Nat.cast_add, Nat.cast_one] at h
  rw [colTreePoly_eval_mpMoment (k + 1 + 2) (by omega),
    colTreePoly_eval_mpMoment (k + 1 + 1) (by omega),
    colTreePoly_eval_mpMoment (k + 1) (by omega)] at h
  apply (mul_left_cancel₀ hγ)
  linear_combination h

end RandomMatrix
