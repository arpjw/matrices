import RandomMatrix.WalkBounds
import Mathlib.Data.Fin.Tuple.Basic

/-! Position-indexed row and column assignments for rooted walks. -/

namespace RandomMatrix

/-- All row positions, including the initial and final rows. -/
def walkRowLabels {p n : ℕ} : {k : ℕ} → Fin p → WalkSteps p n k → (Fin (k + 1) → Fin p)
  | 0, i, _ => fun _ => i
  | _ + 1, i, s => Fin.cons i (walkRowLabels s.1 s.2.2)

/-- All column positions. -/
def walkColLabels {p n : ℕ} : {k : ℕ} → WalkSteps p n k → (Fin k → Fin n)
  | 0, _ => Fin.elim0
  | _ + 1, s => Fin.cons s.2.1 (walkColLabels s.2.2)

/-- Reconstruct the transitions from their row and column assignments. -/
def stepsFromLabels {p n : ℕ} : {k : ℕ} →
    (Fin (k + 1) → Fin p) → (Fin k → Fin n) → WalkSteps p n k
  | 0, _, _ => ()
  | _ + 1, r, c => (r 1, c 0, stepsFromLabels (Fin.tail r) (Fin.tail c))

@[simp] theorem walkRowLabels_zero {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    walkRowLabels i s 0 = i := by
  cases k <;> simp [walkRowLabels]

theorem walkRowLabels_last {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    walkRowLabels i s (Fin.last k) = walkEnd i s := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [walkRowLabels, walkEnd, ih]

theorem labelsFromSteps_inverse {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    stepsFromLabels (walkRowLabels i s) (walkColLabels s) = s := by
  induction k generalizing i with
  | zero => cases s; rfl
  | succ k ih =>
    rcases s with ⟨j, a, t⟩
    simp [stepsFromLabels, walkRowLabels, walkColLabels, ih]

theorem rowsFromLabels_inverse {p n k : ℕ} (r : Fin (k + 1) → Fin p)
    (c : Fin k → Fin n) : walkRowLabels (r 0) (stepsFromLabels r c) = r := by
  induction k with
  | zero =>
    ext j
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    rfl
  | succ k ih =>
    change Fin.cons (r 0) (walkRowLabels (r 1) (stepsFromLabels (Fin.tail r) (Fin.tail c))) = r
    rw [show r 1 = Fin.tail r 0 from rfl, ih, Fin.cons_self_tail]

theorem colsFromLabels_inverse {p n k : ℕ} (r : Fin (k + 1) → Fin p)
    (c : Fin k → Fin n) : walkColLabels (stepsFromLabels r c) = c := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih => simp [stepsFromLabels, walkColLabels, ih]

/-- A rooted walk is exactly a pair of row-position and column-position assignments. -/
def walkLabelsEquiv (p n k : ℕ) :
    (Fin p × WalkSteps p n k) ≃ ((Fin (k + 1) → Fin p) × (Fin k → Fin n)) where
  toFun w := (walkRowLabels w.1 w.2, walkColLabels w.2)
  invFun f := (f.1 0, stepsFromLabels f.1 f.2)
  left_inv w := by simp [labelsFromSteps_inverse]
  right_inv f := by simp [rowsFromLabels_inverse, colsFromLabels_inverse]

/-- The universal entry-position word, before rows or columns receive labels. -/
def positionWord : (k : ℕ) → List (Fin (k + 1) × Fin k)
  | 0 => []
  | k + 1 => (0, 0) :: (1, 0) ::
      (positionWord k).map (fun e => (e.1.succ, e.2.succ))

/-- Applying position labels reproduces the matrix-entry word of the original walk. -/
theorem positionWord_map_labels {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    (positionWord k).map (fun e => (walkRowLabels i s e.1, walkColLabels s e.2)) =
      walkWord i s := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp [positionWord, walkRowLabels, walkColLabels, walkWord, List.map_map,
      Function.comp_def, ih]

/-- The range of the row assignment is the finite set of visited rows. -/
theorem walkRowLabels_range {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    Set.range (walkRowLabels i s) = (walkRows i s : Set (Fin p)) := by
  induction k generalizing i with
  | zero => simp [walkRowLabels, walkRows]
  | succ k ih => simp [walkRowLabels, walkRows, ih]

/-- The range of the column assignment is the finite set of visited columns. -/
theorem walkColLabels_range {p n k : ℕ} (i : Fin p) (s : WalkSteps p n k) :
    Set.range (walkColLabels s) = (walkCols i s : Set (Fin n)) := by
  induction k generalizing i with
  | zero => simp [walkColLabels, walkCols]
  | succ k ih => simp [walkColLabels, walkCols, ih s.1 s.2.2]

end RandomMatrix
