import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Polynomial upper and lower bounds for bounded continuous tests on the nonnegative half-line.
The bounds can be made arbitrarily close on any fixed compact interval. -/

open Set Filter Topology
open scoped BigOperators Polynomial BoundedContinuousFunction

namespace RandomMatrix

/-- Beyond one, a polynomial is bounded by its coefficient mass times any sufficiently high power. -/
theorem polynomial_tail_bound (p : ℝ[X]) (N : ℕ) (hN : p.natDegree ≤ N)
    {x : ℝ} (hx : 1 ≤ x) :
    |p.eval x| ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * x ^ N := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ x) i)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hx (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hN))
    (abs_nonneg _)

/-- Global polynomial bounds with arbitrarily small gap on a prescribed nonnegative interval.
The added high power controls polynomial growth outside the approximation interval. -/
theorem exists_polynomial_sandwich (f : ℝ →ᵇ ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ l u : ℝ[X],
      (∀ x, 0 ≤ x → l.eval x ≤ f x ∧ f x ≤ u.eval x) ∧
      (∀ x ∈ Icc 0 B, u.eval x - l.eval x ≤ ε) := by
  let R := B + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hBR : B / R < 1 := (div_lt_one hR).mpr (by dsimp [R]; linarith)
  have hBR0 : 0 ≤ B / R := div_nonneg hB hR.le
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1
    (fun t => f (R * t)) (f.continuous.comp (continuous_const.mul continuous_id)).continuousOn
    (ε / 4) (by positivity)
  let C : ℝ := ‖f‖ + ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hlim : Tendsto (fun N : ℕ => C * (B / R) ^ N) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hBR0 hBR).const_mul C
  obtain ⟨N, hN, hsmall⟩ := ((eventually_ge_atTop p.natDegree).and
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity)))).exists
  let s : ℝ[X] := Polynomial.C R⁻¹ * Polynomial.X
  let q := p.comp s
  let e : ℝ[X] := Polynomial.C (ε / 4) + Polynomial.C C * s ^ N
  have hs (x : ℝ) : s.eval x = x / R := by
    simp only [s, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]
    ring
  have hq (x : ℝ) : q.eval x = p.eval (x / R) := by
    simp only [q, Polynomial.eval_comp, hs]
  have he (x : ℝ) : e.eval x = ε / 4 + C * (x / R) ^ N := by
    simp only [e, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, hs]
  have herror (x : ℝ) (hx : 0 ≤ x) : |p.eval (x / R) - f x| ≤ e.eval x := by
    rw [he]
    by_cases hxR : x ≤ R
    · have ht : x / R ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hx hR.le, (div_le_one hR).mpr hxR⟩
      have h := hp (x / R) ht
      rw [mul_div_cancel₀ x hR.ne'] at h
      exact h.le.trans (le_add_of_nonneg_right (mul_nonneg hC (pow_nonneg ht.1 _)))
    · have ht : 1 ≤ x / R := (one_le_div hR).mpr (le_of_not_ge hxR)
      calc
        |p.eval (x / R) - f x| ≤ |p.eval (x / R)| + |f x| := abs_sub _ _
        _ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * (x / R) ^ N +
            ‖f‖ * (x / R) ^ N := add_le_add (polynomial_tail_bound p N hN ht)
              ((f.norm_coe_le_norm x).trans (le_mul_of_one_le_right (norm_nonneg f)
                (one_le_pow₀ ht)))
        _ = C * (x / R) ^ N := by dsimp [C]; ring
        _ ≤ ε / 4 + C * (x / R) ^ N := le_add_of_nonneg_left (by positivity)
  refine ⟨q - e, q + e, ?_, ?_⟩
  · intro x hx
    have h := abs_le.mp (herror x hx)
    simp only [Polynomial.eval_sub, Polynomial.eval_add, hq]
    constructor <;> linarith
  · intro x hx
    have hpow : (x / R) ^ N ≤ (B / R) ^ N :=
      pow_le_pow_left₀ (div_nonneg hx.1 hR.le) (div_le_div_of_nonneg_right hx.2 hR.le) N
    have h := mul_le_mul_of_nonneg_left hpow hC
    simp only [Polynomial.eval_add, Polynomial.eval_sub, he]
    linarith

end RandomMatrix
