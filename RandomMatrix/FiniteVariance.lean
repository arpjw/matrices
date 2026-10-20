import RandomMatrix.PatternBudget

/-! Covariance, variance, and Chebyshev bounds for the finite uniform ensemble. -/

open scoped BigOperators Classical
namespace RandomMatrix

theorem average_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    average (fun ω => f ω - g ω) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ average f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun ω _ => h ω))

theorem average_mono {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ => h ω))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

noncomputable def finiteCovariance {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) : ℝ :=
  average (fun ω => f ω * g ω) - average f * average g

noncomputable def finiteVariance {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  average (fun ω => (f ω - average f) ^ 2)

@[simp] theorem finiteVariance_sign : finiteVariance sign = 1 := by
  simp [finiteVariance]

theorem finiteVariance_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    0 ≤ finiteVariance f := average_nonneg _ (fun _ => sq_nonneg _)

theorem finiteVariance_eq_covariance {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    finiteVariance f = finiteCovariance f f := by
  have he (ω : Ω) : (f ω - average f) ^ 2 =
      f ω * f ω - (2 * average f) * f ω + (average f) ^ 2 := by ring
  simp only [finiteVariance, he, average_add, average_sub, average_mul_const, average_const,
    finiteCovariance]
  ring

theorem finiteCovariance_sum {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [Fintype κ]
    (f : ι → Ω → ℝ) (g : κ → Ω → ℝ) :
    finiteCovariance (fun ω => ∑ i, f i ω) (fun ω => ∑ j, g j ω) =
      ∑ i, ∑ j, finiteCovariance (f i) (g j) := by
  simp only [finiteCovariance, Finset.sum_mul, Finset.mul_sum, average_sum,
    Finset.sum_sub_distrib]
  congr 1 <;> exact Finset.sum_comm

theorem finiteCovariance_mul {Ω : Type*} [Fintype Ω] (a b : ℝ) (f g : Ω → ℝ) :
    finiteCovariance (fun ω => a * f ω) (fun ω => b * g ω) =
      a * b * finiteCovariance f g := by
  have he (ω : Ω) : (a * f ω) * (b * g ω) = (a * b) * (f ω * g ω) := by ring
  simp only [finiteCovariance, he, average_mul_const]
  ring

/-- Event probability is an exact uniform fraction, expressed as an average of indicators. -/
noncomputable def finiteProbability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  average (fun ω => if P ω then 1 else 0)

theorem finiteProbability_nonneg {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    0 ≤ finiteProbability P := average_nonneg _ (fun _ => by split_ifs <;> norm_num)

theorem finiteProbability_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    finiteProbability P ≤ 1 := by
  calc
    _ ≤ average (fun _ : Ω => (1 : ℝ)) := average_mono _ _ (fun _ => by split_ifs <;> norm_num)
    _ = _ := average_const _

theorem finiteProbability_eq_card {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    finiteProbability P = (Nat.card {ω // P ω} : ℝ) / Fintype.card Ω := by
  simp [finiteProbability, average, Finset.sum_boole, Fintype.card_subtype,
    Nat.card_eq_fintype_card, div_eq_mul_inv, mul_comm]

/-- Chebyshev's bound around any deterministic center, using its mean-square error. -/
theorem finite_chebyshev_center {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (z ε : ℝ)
    (hε : 0 < ε) :
    finiteProbability (fun ω => ε < |f ω - z|) ≤
      average (fun ω => (f ω - z) ^ 2) / ε ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [mul_comm, finiteProbability, ← average_mul_const]
  apply average_mono
  intro ω
  by_cases h : ε < |f ω - z|
  · simp only [if_pos h, mul_one]
    nlinarith [sq_abs (f ω - z)]
  · simp only [if_neg h, mul_zero]
    exact sq_nonneg _

theorem mean_square_eq_variance_add_bias {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (z : ℝ) :
    average (fun ω => (f ω - z) ^ 2) = finiteVariance f + (average f - z) ^ 2 := by
  rw [finiteVariance_eq_covariance]
  have he (ω : Ω) : (f ω - z) ^ 2 = f ω * f ω - (2 * z) * f ω + z ^ 2 := by ring
  simp only [he, average_add, average_sub, average_mul_const, average_const, finiteCovariance]
  ring

/-- Disjoint words with jointly even counts must each have even counts. -/
theorem disjoint_words_even {ι : Type*} [DecidableEq ι] [BEq ι] [LawfulBEq ι] (v w : List ι)
    (hjoint : ∀ e, Even (v.count e + w.count e))
    (hdis : ¬ ∃ e, e ∈ v ∧ e ∈ w) :
    (∀ e, Even (v.count e)) ∧ (∀ e, Even (w.count e)) := by
  constructor
  · intro e
    by_cases hv : e ∈ v
    · have hw : e ∉ w := fun hw => hdis ⟨e, hv, hw⟩
      simpa [List.count_eq_zero.mpr hw] using hjoint e
    · simp [List.count_eq_zero.mpr hv]
  · intro e
    by_cases hw : e ∈ w
    · have hv : e ∉ v := fun hv => hdis ⟨e, hv, hw⟩
      simpa [List.count_eq_zero.mpr hv] using hjoint e
    · simp [List.count_eq_zero.mpr hw]

/-- Word covariance is exactly zero or one, determined by the two parity profiles. -/
theorem word_covariance_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [BEq ι] [LawfulBEq ι]
    (v w : List ι) :
    finiteCovariance (fun ω : ι → Bool => (v.map (fun e => sign (ω e))).prod)
      (fun ω : ι → Bool => (w.map (fun e => sign (ω e))).prod) =
      if (∀ e, Even (v.count e + w.count e)) ∧
        ¬ ((∀ e, Even (v.count e)) ∧ (∀ e, Even (w.count e))) then 1 else 0 := by
  unfold finiteCovariance
  rw [average_word_pair, average_word, average_word]
  by_cases hv : ∀ e, Even (v.count e)
  · by_cases hw : ∀ e, Even (w.count e)
    · have hj : ∀ e, Even (v.count e + w.count e) := fun e => (hv e).add (hw e)
      simp [hv, hw, hj]
    · by_cases hj : ∀ e, Even (v.count e + w.count e) <;> simp [hv, hw, hj]
  · by_cases hj : ∀ e, Even (v.count e + w.count e) <;> simp [hv, hj]

/-- Disjoint matrix-entry words have exactly zero covariance. -/
theorem word_covariance_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι] [BEq ι] [LawfulBEq ι]
    (v w : List ι) (hdis : ¬ ∃ e, e ∈ v ∧ e ∈ w) :
    finiteCovariance (fun ω : ι → Bool => (v.map (fun e => sign (ω e))).prod)
      (fun ω : ι → Bool => (w.map (fun e => sign (ω e))).prod) = 0 := by
  rw [word_covariance_eq]
  by_cases hj : ∀ e, Even (v.count e + w.count e)
  · have hh := disjoint_words_even v w hj hdis
    simp [hj, hh]
  · simp [hj]

/-- Only overlapping words with even combined multiplicities can contribute covariance. -/
theorem word_covariance_le_overlap {ι : Type*} [Fintype ι] [DecidableEq ι] [BEq ι] [LawfulBEq ι]
    (v w : List ι) :
    finiteCovariance (fun ω : ι → Bool => (v.map (fun e => sign (ω e))).prod)
      (fun ω : ι → Bool => (w.map (fun e => sign (ω e))).prod) ≤
      if (∀ e, Even (v.count e + w.count e)) ∧ (∃ e, e ∈ v ∧ e ∈ w) then 1 else 0 := by
  unfold finiteCovariance
  rw [average_word_pair, average_word, average_word]
  by_cases hj : ∀ e, Even (v.count e + w.count e)
  · by_cases ho : ∃ e, e ∈ v ∧ e ∈ w
    · have hboth : (∀ e, Even (v.count e + w.count e)) ∧ (∃ e, e ∈ v ∧ e ∈ w) := ⟨hj, ho⟩
      rw [if_pos hj, if_pos hboth]
      split_ifs <;> norm_num
    · obtain ⟨hv, hw⟩ := disjoint_words_even v w hj ho
      simp [hj, ho, hv, hw]
  · have hboth : ¬ ((∀ e, Even (v.count e + w.count e)) ∧ (∃ e, e ∈ v ∧ e ∈ w)) :=
      fun h => hj h.1
    rw [if_neg hj, if_neg hboth]
    split_ifs <;> norm_num

end RandomMatrix
