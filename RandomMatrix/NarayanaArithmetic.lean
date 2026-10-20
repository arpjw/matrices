import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Rational binomial expressions and their three-term recurrence, including support boundaries. -/

namespace RandomMatrix

abbrev binomQ (n r : ℕ) : ℚ := n.choose r

/-- A rational expression, not an assumed enumeration. The zeroth polynomial is one. -/
def narayanaQ : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, r + 1 => binomQ (n + 1) (r + 1) * binomQ (n + 1) r / (n + 1)

theorem binomQ_pascal (n r : ℕ) :
    binomQ (n + 1) (r + 1) = binomQ n (r + 1) + binomQ n r := by
  simp [binomQ, Nat.choose_succ_succ, add_comm]

/-- This signed rational identity also holds beyond the support of the binomial coefficient. -/
theorem binomQ_step (n r : ℕ) :
    binomQ n (r + 1) = binomQ n r * ((n : ℚ) - r) / (r + 1) := by
  have hh := Nat.add_one_mul_choose_eq n r
  rw [Nat.choose_succ_succ] at hh
  have hhq : ((n : ℚ) + 1) * binomQ n r =
      (binomQ n r + binomQ n (r + 1)) * ((r : ℚ) + 1) := by exact_mod_cast hh
  apply (eq_div_iff (by positivity)).mpr
  linear_combination -hhq

theorem narayanaQ_pos (n r : ℕ) (hn : 0 < n) :
    narayanaQ n (r + 1) = binomQ n (r + 1) * binomQ n r / n := by
  cases n with
  | zero => omega
  | succ n => simp [narayanaQ]

theorem narayanaQ_zero_right (n : ℕ) (hn : 0 < n) : narayanaQ n 0 = 0 := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem narayanaQ_one_right (n : ℕ) (hn : 0 < n) : narayanaQ n 1 = 1 := by
  rw [narayanaQ_pos n 0 hn]
  simp [binomQ, ne_of_gt hn]

theorem narayanaQ_two_right (n : ℕ) (hn : 0 < n) :
    narayanaQ n 2 = (n : ℚ) * (n - 1) / 2 := by
  rw [narayanaQ_pos n 1 hn, binomQ_step n 1]
  simp only [binomQ, Nat.choose_one_right, Nat.cast_one]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp
  ring

/-- The binomial formula satisfies the same linear recurrence as the tree polynomials. -/
theorem narayanaQ_recurrence (n r : ℕ) (hn : 0 < n) :
    ((n : ℚ) + 3) * narayanaQ (n + 2) r =
      (2 * n + 3) * (narayanaQ (n + 1) r + narayanaQ (n + 1) (r - 1)) -
        n * (narayanaQ n r - 2 * narayanaQ n (r - 1) + narayanaQ n (r - 2)) := by
  rcases r with _ | r
  · simp only [Nat.zero_sub, narayanaQ_zero_right _ hn,
      narayanaQ_zero_right _ (by omega : 0 < n + 1),
      narayanaQ_zero_right _ (by omega : 0 < n + 2)]
    ring
  rcases r with _ | r
  · simp only [narayanaQ_one_right _ hn, narayanaQ_one_right _ (by omega : 0 < n + 1),
      narayanaQ_one_right _ (by omega : 0 < n + 2), narayanaQ_zero_right _ hn, narayanaQ_zero_right _ (by omega : 0 < n + 1)]
    ring
  rcases r with _ | r
  · simp only [Nat.reduceSubDiff, Nat.add_sub_cancel ]
    rw [narayanaQ_two_right _ (by omega), narayanaQ_two_right _ (by omega),
      narayanaQ_two_right _ hn, narayanaQ_one_right _ (by omega),
      narayanaQ_one_right _ hn, narayanaQ_zero_right _ hn]
    push_cast
    ring
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℚ) + 2 ≠ 0 := by positivity
  have hr1 : (r : ℚ) + 1 ≠ 0 := by positivity
  have hr2 : (r : ℚ) + 2 ≠ 0 := by positivity
  have hr3 : (r : ℚ) + 3 ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel,
    show r + 1 + 1 + 1 - 2 = r + 1 by omega]
  rw [narayanaQ_pos _ _ (by omega), narayanaQ_pos _ _ (by omega),
    narayanaQ_pos _ _ (by omega), narayanaQ_pos _ _ hn, narayanaQ_pos _ _ hn,
    narayanaQ_pos _ _ hn]
  simp only [show n + 2 = (n + 1) + 1 by omega, binomQ_pascal]
  rw [binomQ_step n (r + 1 + 1), binomQ_step n (r + 1), binomQ_step n r]
  push_cast
  field_simp
  ring

end RandomMatrix
