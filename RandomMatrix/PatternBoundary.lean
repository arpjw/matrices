import RandomMatrix.PatternBounds

/-! Boundary cases for the dimension-independent pattern coefficients. -/

open scoped Classical
namespace RandomMatrix

theorem blockCount_pos {α : Type*} [Finite α] [Nonempty α] (s : Setoid α) :
    0 < blockCount s := by
  letI : Nonempty (Quotient s) := ⟨Quotient.mk s (Classical.arbitrary α)⟩
  exact Finite.card_pos

@[simp] theorem blockCount_fin_zero (s : Setoid (Fin 0)) : blockCount s = 0 := by
  simp [blockCount, Nat.card_eq_fintype_card]

@[simp] theorem blockCount_fin_one (s : Setoid (Fin 1)) : blockCount s = 1 := by
  have hp := blockCount_pos s
  have hl := blockCount_le s
  omega

/-- There is exactly one order-zero pattern: one row block and no column blocks. -/
theorem patternCoefficient_zero (r c : ℕ) :
    patternCoefficient 0 r c = if r = 1 ∧ c = 0 then 1 else 0 := by
  have hs (q : Setoid (Fin 1) × Setoid (Fin 0)) : PatternSurvives 0 q.1 q.2 := by
    constructor
    · exact q.1.refl 0
    · intro e
      exact Fin.elim0 e.2
  have hcard (α : Type) [Fintype α] [Subsingleton α] :
      Fintype.card (Setoid α) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⊤, fun s => ?_⟩
    apply Setoid.ext
    intro x y
    have hxy : x = y := Subsingleton.elim _ _
    subst y
    change s x x ↔ True
    exact ⟨fun _ => trivial, fun _ => s.refl x⟩
  by_cases h : r = 1 ∧ c = 0 <;>
    simp [patternCoefficient, hs, eq_comm, Nat.card_eq_fintype_card, h, hcard]

/-- The root guarantees a row block at every order. -/
theorem patternCoefficient_zero_rows (k c : ℕ) : patternCoefficient k 0 c = 0 := by
  letI : IsEmpty {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
      PatternSurvives k q.1 q.2 ∧ blockCount q.1 = 0 ∧ blockCount q.2 = c} :=
    ⟨fun q => by
      have hp := blockCount_pos q.1.1
      omega⟩
  simp [patternCoefficient, Nat.card_eq_fintype_card]

/-- Every positive-order pattern has a column block. -/
theorem patternCoefficient_zero_cols {k : ℕ} (hk : 0 < k) (r : ℕ) :
    patternCoefficient k r 0 = 0 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI : IsEmpty {q : Setoid (Fin (k + 1)) × Setoid (Fin k) //
      PatternSurvives k q.1 q.2 ∧ blockCount q.1 = r ∧ blockCount q.2 = 0} :=
    ⟨fun q => by
      have hp := blockCount_pos q.1.2
      omega⟩
  simp [patternCoefficient, Nat.card_eq_fintype_card]

end RandomMatrix
