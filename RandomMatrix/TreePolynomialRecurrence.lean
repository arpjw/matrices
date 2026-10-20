import RandomMatrix.TreeGeneratingSeries

/-! A differential identity turns the quadratic tree equation into a linear recurrence. -/

namespace RandomMatrix

private theorem quadratic_differential_identity {R : Type*} [CommRing R]
    (f df z c : R) (h : f = 1 + z * f * (f + c))
    (hd : df = f * (f + c) + z * df * (f + c) + z * f * df) :
    z * (1 - 2 * (c + 2) * z + c ^ 2 * z ^ 2) * df +
      (1 - (c + 2) * z) * f = 1 + c * z := by
  let L := 1 - c * z - 2 * z * f
  have hD : z * L * df = f - 1 := by
    dsimp [L]
    linear_combination z * hd - h
  have hL : L ^ 2 = 1 - 2 * (c + 2) * z + c ^ 2 * z ^ 2 := by
    dsimp [L]
    linear_combination -4 * z * h
  have hF : L * (f - 1) = 1 + c * z - (1 - (c + 2) * z) * f := by
    dsimp [L]
    linear_combination 2 * h
  rw [← hL]
  linear_combination L * hD + hF

theorem colTreeSeries_differential :
    PowerSeries.X * (1 - 2 * (PowerSeries.C Polynomial.X + 1) * PowerSeries.X +
      (PowerSeries.C Polynomial.X - 1) ^ 2 * PowerSeries.X ^ 2) *
        PowerSeries.derivative (Polynomial ℚ) colTreeSeries +
      (1 - (PowerSeries.C Polynomial.X + 1) * PowerSeries.X) * colTreeSeries =
        1 + (PowerSeries.C Polynomial.X - 1) * PowerSeries.X := by
  have h := colTreeSeries_quadratic
  have hd := congrArg (PowerSeries.derivative (Polynomial ℚ)) h
  simp only [map_add, map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_C,
    Derivation.leibniz, PowerSeries.derivative_X, mul_one, zero_add, sub_zero,
    add_zero, smul_eq_mul] at hd
  have hh := quadratic_differential_identity colTreeSeries
    (PowerSeries.derivative (Polynomial ℚ) colTreeSeries) PowerSeries.X
      (PowerSeries.C Polynomial.X - 1) (by convert h using 1; ring) (by
        convert hd using 1; ring)
  have hc : (PowerSeries.C (Polynomial.X : Polynomial ℚ) - 1) + 2 =
      PowerSeries.C Polynomial.X + 1 := by ring
  rw [hc] at hh
  exact hh

/-- The counting polynomials satisfy the classical three-term Narayana recurrence. -/
theorem colTreePoly_recurrence (n : ℕ) :
    (n + 3 : Polynomial ℚ) * colTreePoly (n + 2) =
      (2 * (n : Polynomial ℚ) + 3) * (Polynomial.X + 1) * colTreePoly (n + 1) -
        (n : Polynomial ℚ) * (Polynomial.X - 1) ^ 2 * colTreePoly n := by
  let a : Polynomial ℚ := Polynomial.X + 1
  let b : Polynomial ℚ := (Polynomial.X - 1) ^ 2
  let aa : Polynomial ℚ := 2 * a
  have hh := congrArg (PowerSeries.coeff (n + 2)) colTreeSeries_differential
  have hexpand :
      PowerSeries.X * (1 - 2 * (PowerSeries.C Polynomial.X + 1) * PowerSeries.X +
        (PowerSeries.C Polynomial.X - 1) ^ 2 * PowerSeries.X ^ 2) *
          PowerSeries.derivative (Polynomial ℚ) colTreeSeries +
        (1 - (PowerSeries.C Polynomial.X + 1) * PowerSeries.X) * colTreeSeries =
      PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) colTreeSeries -
        PowerSeries.C aa *
          (PowerSeries.X * (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) colTreeSeries)) +
        PowerSeries.C b *
          (PowerSeries.X * (PowerSeries.X * (PowerSeries.X *
            PowerSeries.derivative (Polynomial ℚ) colTreeSeries))) + colTreeSeries -
        PowerSeries.C a * (PowerSeries.X * colTreeSeries) := by
    dsimp [aa, a, b]
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one]
    ring
  rw [hexpand] at hh
  have hshift : ∀ m, PowerSeries.coeff m
      (PowerSeries.X * PowerSeries.derivative (Polynomial ℚ) colTreeSeries) =
        colTreePoly m * m := by
    intro m
    cases m with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
    | succ m => simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    hshift, coeff_colTreeSeries, PowerSeries.coeff_one, Nat.add_eq_zero_iff,
    OfNat.ofNat_ne_zero, and_false, if_false, zero_add, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one] at hh
  have hz : PowerSeries.coeff (n + 2)
      ((PowerSeries.C (Polynomial.X : Polynomial ℚ) - 1) * PowerSeries.X) = 0 := by
    rw [← map_one PowerSeries.C, ← map_sub, mul_comm, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_succ_C]
  rw [hz] at hh
  dsimp [aa, a, b] at hh
  linear_combination hh

end RandomMatrix
