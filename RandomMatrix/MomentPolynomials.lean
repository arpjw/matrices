import RandomMatrix.NarayanaCoefficients

/-! The limiting Narayana polynomial, identified with the leading diagonal of the exact expansion. -/

open scoped BigOperators Classical
namespace RandomMatrix

/-- The leading diagonal of the exact coefficient expansion. -/
noncomputable def leadingMoment (k : ℕ) (x : ℝ) : ℝ :=
  ∑ r : Fin (k + 2), ∑ c : Fin (k + 1),
    if r.val + c.val = k + 1 then (patternCoefficient k r c : ℝ) * x ^ (r.val - 1) else 0

/-- The Marchenko-Pastur moment polynomial, with its separate order-zero value. -/
noncomputable def mpMoment (k : ℕ) (x : ℝ) : ℝ :=
  if k = 0 then 1 else
    ∑ j : Fin k, ((k.choose (j.val + 1) : ℝ) * k.choose j.val / k) * x ^ j.val

private theorem leadingMoment_row (k r : ℕ) (x : ℝ) (hr : 0 < r) (hrk : r ≤ k + 1) :
    (∑ c : Fin (k + 1), if r + c.val = k + 1 then
      (patternCoefficient k r c : ℝ) * x ^ (r - 1) else 0) =
      (patternCoefficient k r (k + 1 - r) : ℝ) * x ^ (r - 1) := by
  let c₀ : Fin (k + 1) := ⟨k + 1 - r, by omega⟩
  rw [Finset.sum_eq_single c₀]
  · simp [c₀, show r + (k + 1 - r) = k + 1 by omega]
  · intro c hc hne
    have hbad : r + c.val ≠ k + 1 := by
      intro he
      apply hne
      apply Fin.ext
      dsimp [c₀]
      omega
    simp [hbad]
  · simp

@[simp] theorem leadingMoment_zero (x : ℝ) : leadingMoment 0 x = 1 := by
  simp [leadingMoment, Fin.sum_univ_succ, patternCoefficient_zero]

@[simp] theorem mpMoment_zero (x : ℝ) : mpMoment 0 x = 1 := by simp [mpMoment]

@[simp] theorem mpMoment_one (x : ℝ) : mpMoment 1 x = 1 := by
  norm_num [mpMoment, Fin.sum_univ_succ]

@[simp] theorem mpMoment_two (x : ℝ) : mpMoment 2 x = 1 + x := by
  norm_num [mpMoment, Fin.sum_univ_succ]

/-- The leading coefficient polynomial is precisely the explicit Narayana polynomial. -/
theorem leadingMoment_eq_mpMoment (k : ℕ) (x : ℝ) : leadingMoment k x = mpMoment k x := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  unfold leadingMoment
  rw [Fin.sum_univ_succ]
  have hz : (∑ c : Fin (k + 1), if (0 : ℕ) + c.val = k + 1 then
      (patternCoefficient k 0 c : ℝ) * x ^ (0 - 1) else 0) = 0 := by
    simp [patternCoefficient_zero_rows]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [hz, zero_add]
  have hrow (j : Fin (k + 1)) := leadingMoment_row k (j.val + 1) x (by omega) (by omega)
  simp_rw [hrow]
  rw [Fin.sum_univ_castSucc]
  have hlast : patternCoefficient k (k + 1) (k + 1 - (k + 1)) = 0 := by
    simp [patternCoefficient_zero_cols hkpos]
  simp only [Fin.val_last, Fin.val_castSucc, hlast, Nat.cast_zero, zero_mul, add_zero,
    mpMoment, if_neg hk, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j hj
  have he := patternCoefficient_narayana_rat k (j.val + 1) (k + 1 - (j.val + 1))
    hkpos (by omega) (by omega)
  have heR : (patternCoefficient k (j.val + 1) (k + 1 - (j.val + 1)) : ℝ) =
      (k.choose (j.val + 1) : ℝ) * k.choose j.val / k := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) he
    simpa using hcast
  rw [heR]

end RandomMatrix
