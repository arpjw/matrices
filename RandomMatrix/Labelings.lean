import RandomMatrix.FiniteAverage
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finite.Card

/-! Equality patterns and their exact numbers of injective block labelings. -/

open scoped BigOperators Classical
namespace RandomMatrix

noncomputable instance setoidFintype (α : Type*) [Fintype α] : Fintype (Setoid α) := by
  classical
  exact Fintype.ofInjective (fun s : Setoid α => s.r) (fun _ _ h => Setoid.eq_iff_rel_eq.mpr h)

/-- Assignments with a prescribed equality pattern are injective labelings of its blocks. -/
def kernelFiberEquiv {α β : Type*} (s : Setoid α) :
    {f : α → β // Setoid.ker f = s} ≃ (Quotient s ↪ β) where
  toFun f :=
    { toFun := Quotient.lift f.1 (fun a b hab => by
        change Setoid.ker f.1 a b
        rwa [f.2])
      inj' := by
        intro x y h
        induction x using Quotient.inductionOn with | h a =>
          induction y using Quotient.inductionOn with | h b =>
            apply Quotient.sound
            rw [← f.2]
            exact h }
  invFun e := ⟨fun a => e (Quotient.mk s a), by
    apply Setoid.ext
    intro a b
    exact e.injective.eq_iff.trans Quotient.eq⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply DFunLike.ext
    intro x
    induction x using Quotient.inductionOn with | h a => rfl

/-- Falling factorial multiplicity of one equality pattern. -/
theorem card_kernel_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (s : Setoid α) :
    Nat.card {f : α → β // Setoid.ker f = s} =
      (Fintype.card β).descFactorial (Nat.card (Quotient s)) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (kernelFiberEquiv s),
    Fintype.card_embedding_eq, Nat.card_eq_fintype_card]

/-- Regroup any finite sum according to the equality pattern of its assignments. -/
theorem sum_by_kernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (F : Setoid α → ℕ) :
    (∑ f : α → β, F (Setoid.ker f)) =
      ∑ s : Setoid α, F s * (Fintype.card β).descFactorial (Nat.card (Quotient s)) := by
  classical
  rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv (fun f : α → β => Setoid.ker f))]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Equiv.sigmaFiberEquiv_apply]
  have h (f : {f : α → β // Setoid.ker f = s}) : F (Setoid.ker f.1) = F s := by rw [f.2]
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_kernel_fiber]
  exact Nat.mul_comm _ _

/-- Row and column equality patterns can be grouped independently. -/
theorem sum_by_kernel_pair {α β R C : Type*}
    [Fintype α] [Fintype β] [Fintype R] [Fintype C] [DecidableEq α] [DecidableEq β]
    (F : Setoid α → Setoid β → ℕ) :
    (∑ f : α → R, ∑ g : β → C, F (Setoid.ker f) (Setoid.ker g)) =
      ∑ s : Setoid α, ∑ t : Setoid β,
        F s t * (Fintype.card R).descFactorial (Nat.card (Quotient s)) *
          (Fintype.card C).descFactorial (Nat.card (Quotient t)) := by
  simp_rw [sum_by_kernel (β := C)]
  rw [sum_by_kernel (β := R) (fun s : Setoid α =>
    ∑ t : Setoid β, F s t * (Fintype.card C).descFactorial (Nat.card (Quotient t)))]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Group a weighted finite count by any finite statistic. -/
theorem sum_by_statistic {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (f : α → β) (weight : β → ℕ) :
    (∑ a : α, if P a then weight (f a) else 0) =
      ∑ b : β, Nat.card {a : α // P a ∧ f a = b} * weight b := by
  have hc (b : β) : Nat.card {a : α // P a ∧ f a = b} =
      ∑ a : α, if P a ∧ f a = b then (1 : ℕ) else 0 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
  simp_rw [hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : P a <;> simp [h, ite_mul]

end RandomMatrix
