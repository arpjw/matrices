import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Finite uniform expectation, including factorization over independent coordinates. -/

open scoped BigOperators
namespace RandomMatrix

noncomputable def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

@[simp] theorem average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    average (fun _ : Ω => c) = c := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, h]

theorem average_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul_const {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    average (fun ω => c * f ω) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (f : ι → Ω → ℝ) :
    average (fun ω => ∑ i, f i ω) = ∑ i, average (f i) := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_comm

/-- Uniform averaging over all coordinate assignments factors exactly. -/
theorem average_prod {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    (f : ι → B → ℝ) :
    average (fun ω : ι → B => ∏ i, f i (ω i)) =
      ∏ i, average (f i) := by
  simp only [average, Fintype.card_fun, Nat.cast_pow]
  rw [← Fintype.prod_sum]
  simp [Finset.prod_mul_distrib, ← inv_pow]

end RandomMatrix
