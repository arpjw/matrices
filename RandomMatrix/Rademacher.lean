import RandomMatrix.FiniteAverage
import Mathlib.Algebra.Ring.Parity

/-! Independent fair signs represented by uniform averaging over the finite cube. -/

open scoped BigOperators
namespace RandomMatrix

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem average_sign : average sign = 0 := by
  norm_num [average, sign, Fintype.sum_bool]

/-- Every odd sign moment vanishes; every even sign moment is one. -/
theorem average_sign_pow (k : ℕ) :
    average (fun b => sign b ^ k) = if Even k then 1 else 0 := by
  simp only [average, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool, sign]
  simp only [Bool.false_eq_true, ↓reduceIte, one_pow]
  rw [neg_one_pow_eq_ite]
  split_ifs <;> norm_num

/-- Exact all-order moment factorization for independent signs. -/
theorem average_sign_monomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (powers : ι → ℕ) :
    average (fun ω : ι → Bool => ∏ i, sign (ω i) ^ powers i) =
      ∏ i, if Even (powers i) then (1 : ℝ) else 0 := by
  rw [average_prod (fun i b => sign b ^ powers i)]
  simp_rw [average_sign_pow]

/-- Any monomial with an odd coordinate exponent has expectation zero. -/
theorem average_sign_monomial_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (powers : ι → ℕ) (i : ι) (hi : ¬ Even (powers i)) :
    average (fun ω : ι → Bool => ∏ j, sign (ω j) ^ powers j) = 0 := by
  rw [average_sign_monomial]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- A nonempty square-free sign product has expectation zero. -/
theorem average_character {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) :
    average (fun ω : ι → Bool => ∏ i ∈ s, sign (ω i)) = 0 := by
  have h := average_prod (fun (i : ι) (b : Bool) => if i ∈ s then sign b else 1)
  simp only [Finset.prod_ite_mem_eq] at h
  rw [h]
  obtain ⟨i, hi⟩ := hs
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

/-- The four entries on a rectangle survive averaging iff one side collapses. -/
theorem average_rectangle {P N : Type*} [Fintype P] [Fintype N]
    [DecidableEq P] [DecidableEq N] (i j : P) (a b : N) :
    average (fun ω : P × N → Bool =>
      sign (ω (i, a)) * sign (ω (j, a)) * sign (ω (j, b)) * sign (ω (i, b))) =
      if i = j ∨ a = b then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hf : (fun ω : P × N → Bool =>
        sign (ω (i, a)) * sign (ω (i, a)) * sign (ω (i, b)) * sign (ω (i, b))) =
        fun _ => (1 : ℝ) := by
      funext ω
      calc
        _ = sign (ω (i, a)) ^ 2 * sign (ω (i, b)) ^ 2 := by ring
        _ = 1 := by simp
    rw [hf]
    simp
  · by_cases hab : a = b
    · subst b
      have hf : (fun ω : P × N → Bool =>
          sign (ω (i, a)) * sign (ω (j, a)) * sign (ω (j, a)) * sign (ω (i, a))) =
          fun _ => (1 : ℝ) := by
        funext ω
        calc
          _ = sign (ω (i, a)) ^ 2 * sign (ω (j, a)) ^ 2 := by ring
          _ = 1 := by simp
      rw [hf]
      simp
    · rw [if_neg (not_or.mpr ⟨hij, hab⟩)]
      have h := average_character
        ({(i, a), (j, a), (j, b), (i, b)} : Finset (P × N)) (by simp)
      convert h using 1
      congr 1
      funext ω
      simp [hij, Ne.symm hij, hab, mul_comm, mul_left_comm, mul_assoc]

end RandomMatrix
