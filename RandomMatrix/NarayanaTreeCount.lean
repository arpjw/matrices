import RandomMatrix.TreePolynomialRecurrence
import RandomMatrix.NarayanaArithmetic

/-! Identifying the actual tree-counting polynomial with the rational Narayana formula. -/

open scoped BigOperators Classical
namespace RandomMatrix

@[simp] theorem rowTreePoly_one : rowTreePoly 1 = Polynomial.X := by
  simp [rowTreePoly_succ]

@[simp] theorem colTreePoly_one : colTreePoly 1 = Polynomial.X := by
  simp [colTreePoly_succ]

@[simp] theorem colTreePoly_two : colTreePoly 2 = Polynomial.X + Polynomial.X ^ 2 := by
  rw [colTreePoly_succ]
  simp [Finset.Nat.antidiagonal_succ, pow_two, add_comm]

private theorem coeff_X_mul_of_zero (p : Polynomial ℚ) (hp : p.coeff 0 = 0) (r : ℕ) :
    (Polynomial.X * p).coeff r = p.coeff (r - 1) := by
  cases r with
  | zero => simpa using hp.symm
  | succ r => simp [Polynomial.coeff_X_mul]

private theorem coeff_XX_mul_of_zero (p : Polynomial ℚ) (hp : p.coeff 0 = 0) (r : ℕ) :
    (Polynomial.X * (Polynomial.X * p)).coeff r = p.coeff (r - 2) := by
  rw [coeff_X_mul_of_zero _ (by simp), coeff_X_mul_of_zero p hp]
  congr 1

theorem colTreePoly_coeff_recurrence (n r : ℕ)
    (h0 : (colTreePoly n).coeff 0 = 0) (h1 : (colTreePoly (n + 1)).coeff 0 = 0) :
    ((n : ℚ) + 3) * (colTreePoly (n + 2)).coeff r =
      (2 * n + 3) * ((colTreePoly (n + 1)).coeff r + (colTreePoly (n + 1)).coeff (r - 1)) -
        n * ((colTreePoly n).coeff r - 2 * (colTreePoly n).coeff (r - 1) +
          (colTreePoly n).coeff (r - 2)) := by
  have he : Polynomial.C ((n : ℚ) + 3) * colTreePoly (n + 2) =
      Polynomial.C (2 * (n : ℚ) + 3) *
        (colTreePoly (n + 1) + Polynomial.X * colTreePoly (n + 1)) -
      Polynomial.C (n : ℚ) * (colTreePoly n - Polynomial.C 2 *
        (Polynomial.X * colTreePoly n) + Polynomial.X * (Polynomial.X * colTreePoly n)) := by
    simp only [map_add, map_mul, map_natCast, map_ofNat]
    linear_combination colTreePoly_recurrence n
  have hh := congrArg (fun p : Polynomial ℚ => p.coeff r) he
  simpa only [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_add,
    coeff_X_mul_of_zero _ h0, coeff_X_mul_of_zero _ h1, coeff_XX_mul_of_zero _ h0] using hh

/-- Every coefficient of the actual column-counting tree polynomial has the closed form. -/
theorem colTreePoly_coeff_narayana (n r : ℕ) :
    (colTreePoly n).coeff r = narayanaQ n r := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · cases r <;> simp [narayanaQ, Polynomial.coeff_one]
    · rcases r with _ | _ | r <;> simp [narayanaQ, binomQ, Nat.choose, Polynomial.coeff_X]
    · rcases r with _ | _ | _ | r <;> norm_num [narayanaQ, binomQ, Nat.choose,
        Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
      omega
    · have h0 : (colTreePoly (n + 1)).coeff 0 = 0 := by
        rw [ih _ (by omega) 0, narayanaQ_zero_right _ (by omega)]
      have h1 : (colTreePoly (n + 1 + 1)).coeff 0 = 0 := by
        rw [ih _ (by omega) 0, narayanaQ_zero_right _ (by omega)]
      have hh := colTreePoly_coeff_recurrence (n + 1) r h0 h1
      simp only [ih (n + 1) (by omega), ih (n + 1 + 1) (by omega)] at hh
      have ha := narayanaQ_recurrence (n + 1) r (by omega)
      have hn : ((n + 1 : ℕ) : ℚ) + 3 ≠ 0 := by positivity
      exact (mul_left_cancel₀ hn) (hh.trans ha.symm)

/-- Positive-order row and column refinements have the same polynomial. -/
theorem rowTreePoly_eq_colTreePoly (n : ℕ) (hn : 0 < n) : rowTreePoly n = colTreePoly n := by
  have hh := congrArg (PowerSeries.coeff n) rowTreeSeries_sub_colTreeSeries
  cases n with
  | zero => omega
  | succ n =>
    simp only [map_sub, coeff_rowTreeSeries, coeff_colTreeSeries, PowerSeries.coeff_succ_C,
      PowerSeries.coeff_one, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
      sub_zero] at hh
    exact sub_eq_zero.mp hh

theorem rowTreePoly_coeff_narayana (n r : ℕ) (hn : 0 < n) :
    (rowTreePoly n).coeff r = narayanaQ n r := by
  rw [rowTreePoly_eq_colTreePoly n hn, colTreePoly_coeff_narayana]

/-- Coefficient extraction counts the original finite subtype of ordered tree shapes. -/
theorem rowTreePoly_coeff_card (n r : ℕ) :
    (rowTreePoly n).coeff r =
      (Nat.card {t : OrderedTree // t.numNodes = n ∧ treeRows t = r} : ℚ) := by
  let s := (Tree.treesOfNumNodesEq n).filter (fun t => treeRows t = r)
  have hc : Nat.card {t : OrderedTree // t.numNodes = n ∧ treeRows t = r} = s.card := by
    calc
      _ = Nat.card ↥s := Nat.card_congr (Equiv.subtypeEquivRight (fun t => by simp [s]))
      _ = s.card := by simp
  rw [hc, rowTreePoly, Polynomial.finset_sum_coeff]
  simp [s, Polynomial.coeff_X_pow, eq_comm]

end RandomMatrix
