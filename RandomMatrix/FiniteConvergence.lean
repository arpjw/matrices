import RandomMatrix.FiniteVariance
import Mathlib.Analysis.SpecificLimits.Basic

/-! Convergence in probability on separate finite uniform spaces, without a joint coupling. -/

open Filter Topology
open scoped BigOperators Classical

namespace RandomMatrix

/-- The probability spaces may depend on the sequence index. -/
def FiniteConvergesInProbability {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]
    (F : ∀ m, Ω m → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun m => finiteProbability (fun ω => ε < |F m ω - a|)) atTop (nhds 0)

theorem finiteProbability_mono {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop)
    (h : ∀ ω, P ω → Q ω) : finiteProbability P ≤ finiteProbability Q := by
  apply average_mono
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp [hp]; split_ifs <;> norm_num

theorem finiteProbability_or_le {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop) :
    finiteProbability (fun ω => P ω ∨ Q ω) ≤ finiteProbability P + finiteProbability Q := by
  rw [finiteProbability, finiteProbability, finiteProbability, ← average_add]
  apply average_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

theorem finiteConverges_const {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)] (a : ℝ) :
    FiniteConvergesInProbability (fun _ _ => a : ∀ m, Ω m → ℝ) a := by
  intro ε hε
  simp [finiteProbability, not_lt_of_ge hε.le, average]

theorem FiniteConvergesInProbability.add {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]
    {F G : ∀ m, Ω m → ℝ} {a b : ℝ}
    (hF : FiniteConvergesInProbability F a) (hG : FiniteConvergesInProbability G b) :
    FiniteConvergesInProbability (fun m ω => F m ω + G m ω) (a + b) := by
  intro ε hε
  have hbound (m : ℕ) : finiteProbability (fun ω => ε < |F m ω + G m ω - (a + b)|) ≤
      finiteProbability (fun ω => ε / 2 < |F m ω - a|) +
      finiteProbability (fun ω => ε / 2 < |G m ω - b|) := by
    refine (finiteProbability_mono _ _ fun ω h => ?_).trans (finiteProbability_or_le _ _)
    by_contra hn
    push_neg at hn
    have hab := abs_add_le (F m ω - a) (G m ω - b)
    have he : F m ω + G m ω - (a + b) = (F m ω - a) + (G m ω - b) := by ring
    rw [he] at h
    linarith
  exact squeeze_zero (fun _ => finiteProbability_nonneg _) hbound
    (by simpa using (hF (ε / 2) (by positivity)).add (hG (ε / 2) (by positivity)))

theorem FiniteConvergesInProbability.const_mul {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]
    {F : ∀ m, Ω m → ℝ} {a : ℝ}
    (hF : FiniteConvergesInProbability F a) (c : ℝ) :
    FiniteConvergesInProbability (fun m ω => c * F m ω) (c * a) := by
  by_cases hc : c = 0
  · subst c
    simpa using (finiteConverges_const (Ω := Ω) 0)
  intro ε hε
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hbound (m : ℕ) : finiteProbability (fun ω => ε < |c * F m ω - c * a|) ≤
      finiteProbability (fun ω => ε / |c| < |F m ω - a|) := by
    apply finiteProbability_mono
    intro ω h
    rw [← mul_sub, abs_mul] at h
    exact (div_lt_iff₀ hcpos).mpr (by simpa [mul_comm] using h)
  exact squeeze_zero (fun _ => finiteProbability_nonneg _) hbound
    (hF (ε / |c|) (div_pos hε hcpos))

theorem finiteConverges_sum {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]
    {ι : Type*} (s : Finset ι) (F : ι → ∀ m, Ω m → ℝ) (a : ι → ℝ)
    (h : ∀ i ∈ s, FiniteConvergesInProbability (F i) (a i)) :
    FiniteConvergesInProbability (fun m ω => ∑ i ∈ s, F i m ω) (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (finiteConverges_const (Ω := Ω) 0)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end RandomMatrix
