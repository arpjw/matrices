import RandomMatrix.ContourPositions
import RandomMatrix.ContourEdges

/-! Position labelings extracted from a finite alternating contour. -/

open scoped Classical
namespace RandomMatrix

def listLabels {V : Type*} {n : ℕ} (xs : List V) (h : xs.length = n) (j : Fin n) : V :=
  xs[j.val]'(by omega)

theorem listLabels_range {V : Type*} {n : ℕ} (xs : List V) (h : xs.length = n) :
    Set.range (listLabels xs h) = (xs.toFinset : Set V) := by
  ext x
  simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset]
  constructor
  · rintro ⟨j, rfl⟩
    exact List.getElem_mem _
  · intro hx
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hx
    exact ⟨⟨j, by omega⟩, he⟩

theorem listLabels_ofFn {V : Type*} {n : ℕ} (f : Fin n → V) :
    listLabels (List.ofFn f) (List.length_ofFn) = f := by
  funext j
  simp [listLabels]

theorem listLabels_toList {V : Type*} {n : ℕ} (xs : List V) (h : xs.length = n) :
    List.ofFn (listLabels xs h) = xs := by
  subst n
  simpa only [listLabels] using List.ofFn_getElem xs

theorem listLabels_map {V W : Type*} {n : ℕ} (xs : List V) (h : xs.length = n)
    (f : V → W) (hm : (xs.map f).length = n) :
    listLabels (xs.map f) hm = f ∘ listLabels xs h := by
  funext j
  simp [listLabels]

theorem listLabels_blockCount {V : Type*} {n : ℕ} (xs : List V) (h : xs.length = n) :
    blockCount (Setoid.ker (listLabels xs h)) = xs.toFinset.card := by
  unfold blockCount
  rw [Nat.card_congr (Setoid.quotientKerEquivRange (listLabels xs h)), listLabels_range]
  change Nat.card ↑xs.toFinset = xs.toFinset.card
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem contour_rows_length {V : Type*} {k : ℕ} (u : V) (w : List V) (h : w.length = 2 * k) :
    (evenPositions (u :: w)).length = k + 1 := by
  have hh := (positions_length (u :: w)).1
  simp only [List.length_cons, h] at hh
  omega

theorem contour_cols_length {V : Type*} {k : ℕ} (u : V) (w : List V) (h : w.length = 2 * k) :
    (oddPositions (u :: w)).length = k := by
  have hh := (positions_length (u :: w)).2
  simp only [List.length_cons, h] at hh
  omega

def contourRowLabels {V : Type*} {k : ℕ} (u : V) (w : List V) (h : w.length = 2 * k) :
    Fin (k + 1) → V :=
  listLabels (evenPositions (u :: w)) (contour_rows_length u w h)

def contourColLabels {V : Type*} {k : ℕ} (u : V) (w : List V) (h : w.length = 2 * k) :
    Fin k → V :=
  listLabels (oddPositions (u :: w)) (contour_cols_length u w h)

@[simp] theorem contourRowLabels_zero {V : Type*} {k : ℕ} (u : V) (w : List V)
    (h : w.length = 2 * k) : contourRowLabels u w h 0 = u := rfl

theorem contourRowLabels_map {V W : Type*} {k : ℕ} (u : V) (w : List V)
    (h : w.length = 2 * k) (f : V → W) (hm : (w.map f).length = 2 * k) :
    contourRowLabels (f u) (w.map f) hm = f ∘ contourRowLabels u w h := by
  have he := (positions_map f (u :: w)).1
  simp only [List.map_cons] at he
  funext j
  simp only [contourRowLabels, listLabels, he, List.getElem_map, Function.comp_apply]

theorem contourColLabels_map {V W : Type*} {k : ℕ} (u : V) (w : List V)
    (h : w.length = 2 * k) (f : V → W) (hm : (w.map f).length = 2 * k) :
    contourColLabels (f u) (w.map f) hm = f ∘ contourColLabels u w h := by
  have he := (positions_map f (u :: w)).2
  simp only [List.map_cons] at he
  funext j
  simp only [contourColLabels, listLabels, he, List.getElem_map, Function.comp_apply]

theorem evenPositions_last {V : Type*} {k : ℕ} (xs : List V)
    (h : xs.length = 2 * k + 1) : (evenPositions xs).getLast? = xs.getLast? := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      have hx : xs = [] := by simpa using h
      subst xs
      rfl
  | succ k ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      cases xs with
      | nil => simp at h
      | cons y xs =>
        cases xs with
        | nil => simp at h
        | cons z xs =>
          have hz : (z :: xs).length = 2 * k + 1 := by simp only [List.length_cons] at h ⊢; omega
          simpa only [evenPositions_cons, oddPositions_cons, List.getLast?_cons_cons] using ih _ hz

theorem listLabels_last {V : Type*} {k : ℕ} (xs : List V) (h : xs.length = k + 1) :
    some (listLabels xs h (Fin.last k)) = xs.getLast? := by
  rw [List.getLast?_eq_some_getLast (by intro hh; simp [hh] at h), List.getLast_eq_getElem]
  simp [listLabels, h]

theorem IsOrderedContour.rowLabels_closed {V : Type*} {t : OrderedTree}
    {u : V} {w : List V} (hc : IsOrderedContour t u w) :
    contourRowLabels u w hc.length (Fin.last t.numNodes) = contourRowLabels u w hc.length 0 := by
  rw [contourRowLabels_zero]
  apply Option.some.inj
  exact (listLabels_last (evenPositions (u :: w)) (contour_rows_length u w hc.length)).trans
    ((evenPositions_last (k := t.numNodes) (u :: w) (by simp [hc.length])).trans hc.last)

/-- The unordered entry-position word is exactly the contour's consecutive-edge list. -/
theorem contour_position_edges {V : Type*} {k : ℕ} (u : V) (w : List V)
    (h : w.length = 2 * k) :
    (positionWord k).map
      (fun e => s(contourRowLabels u w h e.1, contourColLabels u w h e.2)) =
        contourEdges u w := by
  induction k generalizing u w with
  | zero =>
    have hw : w = [] := by simpa using h
    subst w
    rfl
  | succ k ih =>
    cases w with
    | nil => simp at h
    | cons v w =>
      cases w with
      | nil => simp at h; omega
      | cons x w =>
        have hw : w.length = 2 * k := by simp only [List.length_cons] at h; omega
        have hr (j : Fin (k + 1)) :
            contourRowLabels u (v :: x :: w) h j.succ = contourRowLabels x w hw j := rfl
        have hc (j : Fin k) :
            contourColLabels u (v :: x :: w) h j.succ = contourColLabels x w hw j := rfl
        simp only [positionWord, List.map_cons, List.map_map, Function.comp_def, hr, hc,
          contourEdges, ih x w hw]
        congr 1
        congr 1
        exact Sym2.eq_swap

end RandomMatrix
