import RandomMatrix.FallingFactorialBounds

/-! Bounds for the normalized labeling weight of an individual surviving pattern. -/

namespace RandomMatrix

noncomputable def normalizedLabelWeight (p n k r c : ℕ) : ℝ :=
  (p.descFactorial r : ℝ) * (n.descFactorial c : ℝ) / ((p : ℝ) * (n : ℝ) ^ k)

noncomputable def powerLabelWeight (p n k r c : ℕ) : ℝ :=
  (p : ℝ) ^ r * (n : ℝ) ^ c / ((p : ℝ) * (n : ℝ) ^ k)

theorem normalizedLabelWeight_eq (p n k r c : ℕ) (hp : 0 < p) (hn : 0 < n) :
    normalizedLabelWeight p n k r c =
      powerLabelWeight p n k r c * descRatio p r * descRatio n c := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold normalizedLabelWeight powerLabelWeight descRatio
  field_simp

/-- Each missing vertex contributes one extra inverse dimension. -/
theorem powerLabelWeight_deficit (p n k r c d : ℕ) (hp : 0 < p) (hn : 0 < n)
    (hr : 0 < r) (hk : r - 1 + c + d = k) :
    powerLabelWeight p n k r c = ((p : ℝ) / n) ^ (r - 1) * (1 / (n : ℝ)) ^ d := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one] at hk ⊢
  subst k
  unfold powerLabelWeight
  simp only [pow_add, pow_succ, div_pow, one_pow]
  field_simp

private theorem ratio_power_bound (p n k r : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hratio : (p : ℝ) / n ≤ B) (hr : r ≤ k + 1) :
    ((p : ℝ) / n) ^ (r - 1) ≤ B ^ k := by
  exact (pow_le_pow_left₀ (by positivity) hratio _).trans
    (pow_le_pow_right₀ hB (by omega))

/-- A single pattern's error relative to its leading monomial, before coefficient weighting. -/
theorem labelWeight_error_bound (p n k r c : ℕ) (B : ℝ) (hp : 0 < p) (hn : 0 < n)
    (hB : 1 ≤ B) (hratio : (p : ℝ) / n ≤ B) (hr : 0 < r)
    (hsupport : r + c ≤ k + 1) :
    |normalizedLabelWeight p n k r c -
        (if r + c = k + 1 then ((p : ℝ) / n) ^ (r - 1) else 0)| ≤
      B ^ k * (((k + 1 : ℕ) : ℝ) ^ 2 * (1 / (p : ℝ) + 1 / (n : ℝ)) + 1 / (n : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : 0 ≤ B := by linarith
  have hpow0 : 0 ≤ ((p : ℝ) / n) ^ (r - 1) := by positivity
  have hpow := ratio_power_bound p n k r B hB hratio (by omega)
  have hdr0 := descRatio_nonneg p r
  have hdc0 := descRatio_nonneg n c
  have hdr1 := descRatio_le_one p r hp
  have hdc1 := descRatio_le_one n c hn
  have hprod0 := mul_nonneg hdr0 hdc0
  have hprod1 : descRatio p r * descRatio n c ≤ 1 := by nlinarith
  have hcoll := one_sub_descRatio_mul_le p n r c hp hn
  have hrR : (r : ℝ) ≤ k + 1 := by exact_mod_cast (show r ≤ k + 1 by omega)
  have hcR : (c : ℝ) ≤ k + 1 := by exact_mod_cast (show c ≤ k + 1 by omega)
  have hrsq : (r : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ r by positivity]
  have hcsq : (c : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ c by positivity]
  have hcollision : 1 - descRatio p r * descRatio n c ≤
      ((k + 1 : ℕ) : ℝ) ^ 2 * (1 / (p : ℝ) + 1 / (n : ℝ)) := by
    calc
      _ ≤ (r : ℝ) ^ 2 / p + (c : ℝ) ^ 2 / n := hcoll
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ 2 / p + ((k + 1 : ℕ) : ℝ) ^ 2 / n :=
        add_le_add (div_le_div_of_nonneg_right hrsq hpR.le)
          (div_le_div_of_nonneg_right hcsq hnR.le)
      _ = _ := by ring
  rw [normalizedLabelWeight_eq p n k r c hp hn]
  by_cases hlead : r + c = k + 1
  · rw [if_pos hlead, powerLabelWeight_deficit p n k r c 0 hp hn hr (by omega)]
    simp only [pow_zero, mul_one]
    have he : |((p : ℝ) / n) ^ (r - 1) * descRatio p r * descRatio n c -
        ((p : ℝ) / n) ^ (r - 1)| =
        ((p : ℝ) / n) ^ (r - 1) * (1 - descRatio p r * descRatio n c) := by
      rw [abs_of_nonpos]
      · ring
      · nlinarith [mul_nonneg hpow0 (sub_nonneg.mpr hprod1)]
    rw [he]
    apply (mul_le_mul hpow hcollision (sub_nonneg.mpr hprod1) (pow_nonneg hB0 k)).trans
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (pow_nonneg hB0 k)
  · let d := k + 1 - (r + c)
    have hd : 0 < d := by dsimp [d]; omega
    rw [if_neg hlead, sub_zero, powerLabelWeight_deficit p n k r c d hp hn hr (by dsimp [d]; omega)]
    rw [abs_of_nonneg (by positivity)]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one hnR).mpr hn1
    have hdpow : (1 / (n : ℝ)) ^ d ≤ 1 / (n : ℝ) := by
      obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
      rw [he, pow_succ]
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) hinv)
    calc
      _ = (((p : ℝ) / n) ^ (r - 1) * (1 / (n : ℝ)) ^ d) *
          (descRatio p r * descRatio n c) := by ring
      _ ≤ ((p : ℝ) / n) ^ (r - 1) * (1 / (n : ℝ)) ^ d :=
        mul_le_of_le_one_right (by positivity) hprod1
      _ ≤ B ^ k * (1 / (n : ℝ)) := mul_le_mul hpow hdpow (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

end RandomMatrix
