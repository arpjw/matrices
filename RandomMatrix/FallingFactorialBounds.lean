import RandomMatrix.NarayanaCoefficients
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit bounds for the loss from requiring distinct labels. -/

namespace RandomMatrix

/-- Fraction of ordered label assignments with no collisions. -/
noncomputable def descRatio (p r : ℕ) : ℝ := (p.descFactorial r : ℝ) / (p : ℝ) ^ r

theorem descRatio_nonneg (p r : ℕ) : 0 ≤ descRatio p r := by
  unfold descRatio
  positivity

theorem descRatio_le_one (p r : ℕ) (hp : 0 < p) : descRatio p r ≤ 1 := by
  unfold descRatio
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Nat.descFactorial_le_pow p r

@[simp] theorem descRatio_zero (p : ℕ) : descRatio p 0 = 1 := by simp [descRatio]

theorem descRatio_succ (p r : ℕ) :
    descRatio p (r + 1) = ((p - r : ℕ) : ℝ) / p * descRatio p r := by
  unfold descRatio
  rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
  ring

/-- A uniform collision bound, valid even when there are fewer labels than positions. -/
theorem one_sub_descRatio_le (p r : ℕ) (hp : 0 < p) :
    1 - descRatio p r ≤ (r : ℝ) ^ 2 / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  induction r with
  | zero => simp
  | succ r ih =>
    rw [descRatio_succ p r]
    by_cases hr : r ≤ p
    · rw [Nat.cast_sub hr]
      have hd := descRatio_le_one p r hp
      have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ (r : ℝ) / p by positivity)
      have he : (p - (r : ℝ)) / p = 1 - (r : ℝ) / p := by field_simp
      rw [he]
      have hsq : (r : ℝ) ^ 2 / p + r / p ≤ ((r : ℝ) + 1) ^ 2 / p := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ (le_of_lt hpR)
        nlinarith [show (0 : ℝ) ≤ r by positivity]
      push_cast
      nlinarith
    · have hpr : p ≤ r := by omega
      rw [Nat.sub_eq_zero_of_le hpr]
      simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero]
      apply (le_div_iff₀ hpR).mpr
      have hh : (p : ℝ) ≤ r := by exact_mod_cast hpr
      push_cast
      nlinarith [show (0 : ℝ) ≤ r by positivity]

/-- Multiplying independent row and column labeling fractions adds their error bounds. -/
theorem one_sub_descRatio_mul_le (p n r c : ℕ) (hp : 0 < p) (hn : 0 < n) :
    1 - descRatio p r * descRatio n c ≤ (r : ℝ) ^ 2 / p + (c : ℝ) ^ 2 / n := by
  have hp0 := descRatio_nonneg p r
  have hp1 := descRatio_le_one p r hp
  have hn1 := descRatio_le_one n c hn
  have he := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hn1)
  have hr := one_sub_descRatio_le p r hp
  have hc := one_sub_descRatio_le n c hn
  nlinarith

end RandomMatrix
