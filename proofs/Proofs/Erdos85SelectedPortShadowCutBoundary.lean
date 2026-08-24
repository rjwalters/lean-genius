import Mathlib

/-!
# Owner-factor boundary as a selected-port shadow cut

Each secondary label has two physical owner ports.  Its owner-factor
boundary is one exactly when one port is selected and the other is not,
which is exactly when the corresponding labelled shadow edge crosses the
selected-port cut.  Restricting to inactive labels preserves this literal
occurrence identification.

This formalizes `(73rnz_cjibkzzq)--(73rnz_cjibkzzr)` and connects the
two-label shadow-star split to the remaining owner-factor boundary/curl
decomposition.
-/

namespace Erdos85

/-- Embed a selected-port bit in `ZMod 2`. -/
def selectedPortBit {P : Type*} (selected : P → Bool) (p : P) : ZMod 2 :=
  if selected p then 1 else 0

/-- Boundary coefficient of the owner-factor edge indexed by a label with
the two physical endpoint ports `left y` and `right y`. -/
def ownerFactorSelectedBoundary {L P : Type*}
    (selected : P → Bool) (left right : L → P) (y : L) : ZMod 2 :=
  selectedPortBit selected (left y) + selectedPortBit selected (right y)

/-- Secondary labels whose physical shadow edge crosses the selected-port
cut, restricted to the inactive label census. -/
def inactiveSelectedPortShadowCutLabels {L P : Type*} [DecidableEq L]
    (labels : Finset L) (active : L → Bool)
    (selected : P → Bool) (left right : L → P) : Finset L :=
  labels.filter fun y => !active y && (selected (left y) != selected (right y))

/-- Boundary one is precisely a selected-to-complementary physical shadow
edge. -/
theorem ownerFactorSelectedBoundary_eq_one_iff_crosses
    {L P : Type*} (selected : P → Bool) (left right : L → P) (y : L) :
    ownerFactorSelectedBoundary selected left right y = 1 ↔
      selected (left y) ≠ selected (right y) := by
  cases hl : selected (left y) <;> cases hr : selected (right y) <;>
    simp [ownerFactorSelectedBoundary, selectedPortBit, hl, hr]

/-- A crossing has the canonical two possible orientations: selected left
to complementary right, or selected right to complementary left. -/
theorem selectedPort_crossing_orientation
    {L P : Type*} (selected : P → Bool) (left right : L → P) (y : L)
    (hcross : selected (left y) ≠ selected (right y)) :
    (selected (left y) = true ∧ selected (right y) = false) ∨
      (selected (right y) = true ∧ selected (left y) = false) := by
  cases hl : selected (left y) <;> cases hr : selected (right y) <;>
    simp_all

/-- **Inactive boundary/cut occurrence equivalence (`73rnz_cjibkzzr`).**
Membership in the literal inactive selected-port shadow cut is equivalent
to inactivity together with owner-factor boundary coefficient one. -/
theorem mem_inactiveSelectedPortShadowCutLabels_iff
    {L P : Type*} [DecidableEq L]
    (labels : Finset L) (active : L → Bool)
    (selected : P → Bool) (left right : L → P) (y : L) :
    y ∈ inactiveSelectedPortShadowCutLabels labels active selected left right ↔
      y ∈ labels ∧ active y = false ∧
        ownerFactorSelectedBoundary selected left right y = 1 := by
  simp only [inactiveSelectedPortShadowCutLabels, Finset.mem_filter,
    Bool.and_eq_true]
  rw [ownerFactorSelectedBoundary_eq_one_iff_crosses]
  cases ha : active y <;>
    cases hl : selected (left y) <;> cases hr : selected (right y) <;>
      simp_all

/-- The inactive selected-port shadow-cut cardinality is exactly the sum of
the inactive owner-factor boundary coefficients.  This is the aggregate
parity form of the occurrence bijection. -/
theorem card_inactiveSelectedPortShadowCutLabels_eq_boundary_sum
    {L P : Type*} [DecidableEq L]
    (labels : Finset L) (active : L → Bool)
    (selected : P → Bool) (left right : L → P) :
    ((inactiveSelectedPortShadowCutLabels labels active selected left right).card :
        ZMod 2) =
      ∑ y ∈ labels.filter (fun y => !active y),
        ownerFactorSelectedBoundary selected left right y := by
  classical
  let inactiveLabels := labels.filter fun y => !active y
  have hcut :
      inactiveLabels.filter (fun y => selected (left y) ≠ selected (right y)) =
        inactiveSelectedPortShadowCutLabels labels active selected left right := by
    ext y
    simp [inactiveLabels, inactiveSelectedPortShadowCutLabels]
    tauto
  change ((inactiveSelectedPortShadowCutLabels labels active selected left right).card :
      ZMod 2) =
    ∑ y ∈ inactiveLabels, ownerFactorSelectedBoundary selected left right y
  symm
  calc
    (∑ y ∈ inactiveLabels, ownerFactorSelectedBoundary selected left right y) =
        ∑ y ∈ inactiveLabels,
          if selected (left y) ≠ selected (right y) then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro y _hy
      cases hl : selected (left y) <;> cases hr : selected (right y) <;>
        simp [ownerFactorSelectedBoundary, selectedPortBit, hl, hr]
      change (2 : ZMod 2) = 0
      decide
    _ = ∑ _y ∈ inactiveLabels.filter
          (fun y => selected (left y) ≠ selected (right y)), (1 : ZMod 2) := by
      exact (Finset.sum_filter (s := inactiveLabels)
        (p := fun y => selected (left y) ≠ selected (right y))
        (f := fun _ => (1 : ZMod 2))).symm
    _ = ((inactiveLabels.filter
          (fun y => selected (left y) ≠ selected (right y))).card : ZMod 2) := by
      simp
    _ = ((inactiveSelectedPortShadowCutLabels labels active selected left right).card :
          ZMod 2) := by rw [hcut]

end Erdos85

#print axioms Erdos85.ownerFactorSelectedBoundary_eq_one_iff_crosses
#print axioms Erdos85.selectedPort_crossing_orientation
#print axioms Erdos85.mem_inactiveSelectedPortShadowCutLabels_iff
#print axioms Erdos85.card_inactiveSelectedPortShadowCutLabels_eq_boundary_sum
