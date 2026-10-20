import RandomMatrix.PairCounting
import RandomMatrix.LabelWeightBounds

/-! A dimension-independent bound for the normalized count of connected even walk pairs. -/

open scoped BigOperators Classical
namespace RandomMatrix

/-- All joint partition pairs fit in this explicit, deliberately conservative budget. -/
def pairPatternBudget (k : ℕ) : ℕ :=
  (2 * (k + 1)) ^ (2 * (k + 1)) * (2 * k) ^ (2 * k)

theorem card_setoid_le_fun (α : Type*) [Fintype α] :
    Fintype.card (Setoid α) ≤ (Fintype.card α) ^ Fintype.card α := by
  have hi : Function.Injective (fun s : Setoid α => (representativeLabeling s).val) := by
    intro s t h
    calc
      s = Setoid.ker (representativeLabeling s).val := (representativeLabeling s).property.symm
      _ = Setoid.ker (representativeLabeling t).val := congrArg Setoid.ker h
      _ = t := (representativeLabeling t).property
  simpa using Fintype.card_le_of_injective _ hi

theorem card_pair_patterns_le (k : ℕ) :
    Fintype.card (Setoid (PairRows k)) * Fintype.card (Setoid (PairCols k)) ≤
      pairPatternBudget k := by
  have h := Nat.mul_le_mul (card_setoid_le_fun (PairRows k)) (card_setoid_le_fun (PairCols k))
  simpa [PairRows, PairCols, pairPatternBudget, two_mul] using h

/-- A normalized labeling weight on or below the leading diagonal is uniformly bounded. -/
theorem normalizedLabelWeight_le {p n k r c : ℕ} (hp : 0 < p) (hn : 0 < n)
    (B : ℝ) (hB : 1 ≤ B) (hratio : (p : ℝ) / n ≤ B)
    (hr : 0 < r) (hs : r + c ≤ k + 1) : normalizedLabelWeight p n k r c ≤ B ^ k := by
  have hB0 : 0 ≤ B := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdr0 := descRatio_nonneg p r
  have hdc0 := descRatio_nonneg n c
  have hdr1 := descRatio_le_one p r hp
  have hdc1 := descRatio_le_one n c hn
  have hprod : descRatio p r * descRatio n c ≤ 1 := by nlinarith
  have hpow : 0 ≤ powerLabelWeight p n k r c := by unfold powerLabelWeight; positivity
  let d := k + 1 - (r + c)
  calc
    _ = powerLabelWeight p n k r c * (descRatio p r * descRatio n c) := by
      rw [normalizedLabelWeight_eq p n k r c hp hn]; ring
    _ ≤ powerLabelWeight p n k r c := mul_le_of_le_one_right hpow hprod
    _ = ((p : ℝ) / n) ^ (r - 1) * (1 / (n : ℝ)) ^ d :=
      powerLabelWeight_deficit p n k r c d hp hn hr (by dsimp [d]; omega)
    _ ≤ ((p : ℝ) / n) ^ (r - 1) := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by positivity) ((div_le_one hnR).mpr hn1))
    _ ≤ B ^ (r - 1) := pow_le_pow_left₀ (by positivity) hratio _
    _ ≤ B ^ k := pow_le_pow_right₀ hB (by omega)

/-- The paired count has one fewer free dimension than the variance denominator. -/
theorem pairWalkCount_normalized_le {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (k : ℕ) (B : ℝ) (hB : 1 ≤ B) (hratio : (p : ℝ) / n ≤ B) :
    (pairWalkCount p n k : ℝ) / ((p : ℝ) * (n : ℝ) ^ (2 * k)) ≤
      (pairPatternBudget k : ℝ) * B ^ (2 * k) := by
  have hB0 : 0 ≤ B := by linarith
  have he : (pairWalkCount p n k : ℝ) / ((p : ℝ) * (n : ℝ) ^ (2 * k)) =
      ∑ r : Setoid (PairRows k), ∑ c : Setoid (PairCols k),
        if PairPatternSurvives k r c then
          normalizedLabelWeight p n (2 * k) (blockCount r) (blockCount c) else 0 := by
    rw [pairWalkCount_by_patterns]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero, normalizedLabelWeight,
      div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul]
  rw [he]
  calc
    _ ≤ ∑ _r : Setoid (PairRows k), ∑ _c : Setoid (PairCols k), B ^ (2 * k) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro c hc
      split_ifs with hs
      · exact normalizedLabelWeight_le hp hn B hB hratio (pair_row_blocks_pos r)
          (pair_surviving_block_bound r c hs)
      · positivity
    _ = ((Fintype.card (Setoid (PairRows k)) * Fintype.card (Setoid (PairCols k)) : ℕ) : ℝ) *
        B ^ (2 * k) := by simp [Nat.cast_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_pair_patterns_le k) (by positivity)

end RandomMatrix
