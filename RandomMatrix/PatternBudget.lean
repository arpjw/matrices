import RandomMatrix.NarayanaCoefficients

/-! A deliberately conservative dimension-independent bound for all surviving patterns. -/

open scoped BigOperators Classical
namespace RandomMatrix

/-- Encoding a partition by its canonical representative labels bounds its cardinality. -/
theorem card_setoid_fin_le (m : ℕ) : Fintype.card (Setoid (Fin m)) ≤ m ^ m := by
  have hi : Function.Injective (fun s : Setoid (Fin m) => (representativeLabeling s).val) := by
    intro s t h
    calc
      s = Setoid.ker (representativeLabeling s).val := (representativeLabeling s).property.symm
      _ = Setoid.ker (representativeLabeling t).val := congrArg Setoid.ker h
      _ = t := (representativeLabeling t).property
  simpa using Fintype.card_le_of_injective _ hi

/-- An explicit upper bound on the number of coefficient slots times their maximum size. -/
def patternBudget (k : ℕ) : ℕ := (k + 2) * (k + 1) * ((k + 1) ^ (k + 1) * k ^ k)

theorem patternCoefficient_le_budget_term (k r c : ℕ) :
    patternCoefficient k r c ≤ (k + 1) ^ (k + 1) * k ^ k := by
  unfold patternCoefficient
  rw [Nat.card_eq_fintype_card]
  calc
    _ ≤ Fintype.card (Setoid (Fin (k + 1)) × Setoid (Fin k)) := Fintype.card_subtype_le _
    _ = Fintype.card (Setoid (Fin (k + 1))) * Fintype.card (Setoid (Fin k)) := Fintype.card_prod _ _
    _ ≤ _ := Nat.mul_le_mul (card_setoid_fin_le (k + 1)) (card_setoid_fin_le k)

theorem sum_patternCoefficient_le_budget (k : ℕ) :
    (∑ r : Fin (k + 2), ∑ c : Fin (k + 1), patternCoefficient k r c) ≤ patternBudget k := by
  calc
    _ ≤ ∑ _r : Fin (k + 2), ∑ _c : Fin (k + 1), (k + 1) ^ (k + 1) * k ^ k := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro c hc
      exact patternCoefficient_le_budget_term k r c
    _ = _ := by simp [patternBudget, Nat.mul_assoc]

end RandomMatrix
