import RandomMatrix.Covariance
import RandomMatrix.WordMoments

/-! Closed alternating walks and the exact all-order trace moment formula. -/

open scoped BigOperators
namespace RandomMatrix

/-- Each step records a next row, an intervening column, and the remaining steps. -/
def WalkSteps (p n : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin p × Fin n × WalkSteps p n k

instance walkStepsFintype (p n : ℕ) : (k : ℕ) → Fintype (WalkSteps p n k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 =>
    haveI := walkStepsFintype p n k
    inferInstanceAs (Fintype (Fin p × Fin n × WalkSteps p n k))

/-- The final row after the given number of row-column-row steps. -/
def walkEnd {p n : ℕ} : {k : ℕ} → Fin p → WalkSteps p n k → Fin p
  | 0, i, _ => i
  | _ + 1, _, s => walkEnd s.1 s.2.2

/-- The matrix-entry coordinates visited by a walk, with repetitions retained. -/
def walkWord {p n : ℕ} : {k : ℕ} → Fin p → WalkSteps p n k → List (Fin p × Fin n)
  | 0, _, _ => []
  | _ + 1, i, s => (i, s.2.1) :: (s.1, s.2.1) :: walkWord s.1 s.2.2

theorem walkWord_length {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    (walkWord i s).length = 2 * k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [walkWord, ih, Nat.mul_add, Nat.add_assoc]

/-- An unnormalized Gram-matrix entry is the sum over all walks with fixed endpoints. -/
theorem gram_pow_walks {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (k : ℕ) (i j : Fin p) :
    ((X * X.transpose) ^ k) i j =
      ∑ s : WalkSteps p n k, if walkEnd i s = j then
        ((walkWord i s).map (fun e => X e.1 e.2)).prod else 0 := by
  induction k generalizing i with
  | zero => simp [WalkSteps, walkEnd, walkWord, Matrix.one_apply]
  | succ k ih =>
    simp only [pow_succ', Matrix.mul_apply, Matrix.transpose_apply, ih,
      WalkSteps, Fintype.sum_prod_type, walkEnd, walkWord,
      List.map_cons, List.prod_cons, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> ring

/-- The trace expansion holds at every order, including the empty walk at order zero. -/
theorem trace_covariance_pow_walks {p n : ℕ} (X : Matrix (Fin p) (Fin n) ℝ)
    (k : ℕ) :
    Matrix.trace (covariance X ^ k) = (n : ℝ)⁻¹ ^ k *
      ∑ i, ∑ s : WalkSteps p n k, if walkEnd i s = i then
        ((walkWord i s).map (fun e => X e.1 e.2)).prod else 0 := by
  simp only [covariance, smul_pow, Matrix.trace, Matrix.diag_apply,
    Matrix.smul_apply, smul_eq_mul, gram_pow_walks, Finset.mul_sum]

/-- A rooted walk survives the ensemble average exactly when it is closed and even. -/
def IsEvenClosedWalk {p n k : ℕ} (w : Fin p × WalkSteps p n k) : Prop :=
  walkEnd w.1 w.2 = w.1 ∧ ∀ e, Even ((walkWord w.1 w.2).count e)

instance isEvenClosedWalkDecidable {p n k : ℕ} (w : Fin p × WalkSteps p n k) :
    Decidable (IsEvenClosedWalk w) := by
  unfold IsEvenClosedWalk
  infer_instance

/-- Number of labeled rooted closed alternating walks with even entry multiplicities. -/
noncomputable def evenClosedWalkCount (p n k : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin p × WalkSteps p n k // IsEvenClosedWalk w}

theorem evenClosedWalkCount_eq_sum (p n k : ℕ) :
    (evenClosedWalkCount p n k : ℝ) =
      ∑ i, ∑ s : WalkSteps p n k,
        if IsEvenClosedWalk (i, s) then (1 : ℝ) else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun w : Fin p × WalkSteps p n k =>
    if IsEvenClosedWalk w then (1 : ℝ) else 0), Finset.sum_boole]
  simp [evenClosedWalkCount, Fintype.card_subtype]

/-- Averaging the trace expansion removes exactly the words with an odd multiplicity. -/
theorem average_trace_pow_walks (p n k : ℕ) :
    average (fun ω : Fin p × Fin n → Bool => Matrix.trace (covariance (signMatrix ω) ^ k)) =
      (n : ℝ)⁻¹ ^ k * evenClosedWalkCount p n k := by
  classical
  simp_rw [trace_covariance_pow_walks]
  rw [average_mul_const]
  simp_rw [average_sum]
  rw [evenClosedWalkCount_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : walkEnd i s = i
  · simp only [h, ↓reduceIte, signMatrix, average_word, IsEvenClosedWalk, true_and]
  · simp [h, IsEvenClosedWalk]

/-- Exact finite-dimensional walk counting for every normalized moment order. -/
theorem expected_moment_eq_walk_count {p n : ℕ} (hp : 0 < p) (hn : 0 < n) (k : ℕ) :
    average (fun ω : Fin p × Fin n → Bool => normalizedMoment (signMatrix ω) k) =
      (evenClosedWalkCount p n k : ℝ) / ((p : ℝ) * (n : ℝ) ^ k) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [normalizedMoment, average_mul_const, average_trace_pow_walks]
  rw [inv_pow]
  field_simp

theorem evenClosedWalkCount_zero (p n : ℕ) : evenClosedWalkCount p n 0 = p := by
  have h := evenClosedWalkCount_eq_sum p n 0
  simp [IsEvenClosedWalk, WalkSteps, walkEnd, walkWord] at h
  exact_mod_cast h

end RandomMatrix
