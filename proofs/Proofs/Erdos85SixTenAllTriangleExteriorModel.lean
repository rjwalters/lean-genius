import Mathlib

/-!
# Exterior-pair models for the all-triangle `6+10` block

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The internal ambient graph is `C6 ⊔ C10`.  The two possible defect graphs
have the same short and cross blocks and differ only in the long antipodal
support.  The exterior-pair relation is obtained by removing defect pairs and
pairs with an internal common ambient neighbour.
-/

namespace Erdos85

abbrev SixTenVertex := ZMod 6 ⊕ ZMod 10

def sixTenSameSign : SixTenVertex → SixTenVertex → Prop
  | Sum.inl i, Sum.inl j => i.val % 2 = j.val % 2
  | Sum.inr i, Sum.inr j => i.val % 2 = j.val % 2
  | Sum.inl i, Sum.inr j => i.val % 2 = j.val % 2
  | Sum.inr i, Sum.inl j => i.val % 2 = j.val % 2

instance : DecidableRel sixTenSameSign := by
  intro x y
  cases x <;> cases y <;> unfold sixTenSameSign <;> infer_instance

def sixTenAmbientAdj : SixTenVertex → SixTenVertex → Prop
  | Sum.inl i, Sum.inl j => j - i = 1 ∨ j - i = 5
  | Sum.inr i, Sum.inr j => j - i = 1 ∨ j - i = 9
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => False

instance : DecidableRel sixTenAmbientAdj := by
  intro x y
  cases x <;> cases y <;> unfold sixTenAmbientAdj <;> infer_instance

def sixTenLowDefectAdj : SixTenVertex → SixTenVertex → Prop
  | Sum.inl i, Sum.inl j => j - i = 1 ∨ j - i = 5
  | Sum.inr i, Sum.inr j =>
      j - i = 1 ∨ j - i = 2 ∨ j - i = 3 ∨
        j - i = 7 ∨ j - i = 8 ∨ j - i = 9
  | Sum.inl i, Sum.inr j => sixTenSameSign (Sum.inl i) (Sum.inr j)
  | Sum.inr i, Sum.inl j => sixTenSameSign (Sum.inr i) (Sum.inl j)

instance : DecidableRel sixTenLowDefectAdj := by
  intro x y
  cases x <;> cases y <;> unfold sixTenLowDefectAdj <;> infer_instance

def sixTenHighDefectAdj : SixTenVertex → SixTenVertex → Prop
  | Sum.inl i, Sum.inl j => j - i = 1 ∨ j - i = 5
  | Sum.inr i, Sum.inr j =>
      j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 6 ∨ j - i = 7 ∨ j - i = 9
  | Sum.inl i, Sum.inr j => sixTenSameSign (Sum.inl i) (Sum.inr j)
  | Sum.inr i, Sum.inl j => sixTenSameSign (Sum.inr i) (Sum.inl j)

instance : DecidableRel sixTenHighDefectAdj := by
  intro x y
  cases x <;> cases y <;> unfold sixTenHighDefectAdj <;> infer_instance

def sixTenExteriorPairAdj
    (D : SixTenVertex → SixTenVertex → Prop)
    (x y : SixTenVertex) : Prop :=
  x ≠ y ∧ ¬ D x y ∧
    ¬ ∃ z : SixTenVertex, sixTenAmbientAdj x z ∧ sixTenAmbientAdj y z

instance (D : SixTenVertex → SixTenVertex → Prop) [DecidableRel D] :
    DecidableRel (sixTenExteriorPairAdj D) := by
  intro x y
  unfold sixTenExteriorPairAdj
  infer_instance

def sixTenExteriorPairDegree
    (D : SixTenVertex → SixTenVertex → Prop) [DecidableRel D]
    (x : SixTenVertex) : ℕ :=
  ((Finset.univ : Finset SixTenVertex).filter
    (sixTenExteriorPairAdj D x)).card

/-- On the short shore, exterior ownership is the antipodal matching. -/
theorem sixTenLow_short_exteriorPairAdj_iff (i j : ZMod 6) :
    sixTenExteriorPairAdj sixTenLowDefectAdj (Sum.inl i) (Sum.inl j) ↔
      j - i = 3 := by
  revert i j
  decide

/-- Across shores, exterior ownership is exactly sign inequality. -/
theorem sixTenLow_cross_exteriorPairAdj_iff (i : ZMod 6) (j : ZMod 10) :
    sixTenExteriorPairAdj sixTenLowDefectAdj (Sum.inl i) (Sum.inr j) ↔
      ¬ sixTenSameSign (Sum.inl i) (Sum.inr j) := by
  revert i j
  decide

/-- In the surviving `{\u00b12,\u00b13}` branch, long-shore exterior pairs have
exactly offsets `{\u00b14,5}`. -/
theorem sixTenLow_long_exteriorPairAdj_iff (i j : ZMod 10) :
    sixTenExteriorPairAdj sixTenLowDefectAdj (Sum.inr i) (Sum.inr j) ↔
      j - i = 4 ∨ j - i = 5 ∨ j - i = 6 := by
  revert i j
  decide

/-- The high branch has the same short antipodal exterior matching. -/
theorem sixTenHigh_short_exteriorPairAdj_iff (i j : ZMod 6) :
    sixTenExteriorPairAdj sixTenHighDefectAdj (Sum.inl i) (Sum.inl j) ↔
      j - i = 3 := by
  revert i j
  decide

/-- The high branch also has the same opposite-sign cross exterior pairs. -/
theorem sixTenHigh_cross_exteriorPairAdj_iff (i : ZMod 6) (j : ZMod 10) :
    sixTenExteriorPairAdj sixTenHighDefectAdj (Sum.inl i) (Sum.inr j) ↔
      ¬ sixTenSameSign (Sum.inl i) (Sum.inr j) := by
  revert i j
  decide

/-- Only the long antipodal matching survives as a high-branch exterior pair. -/
theorem sixTenHigh_long_exteriorPairAdj_iff (i j : ZMod 10) :
    sixTenExteriorPairAdj sixTenHighDefectAdj (Sum.inr i) (Sum.inr j) ↔
      j - i = 5 := by
  revert i j
  decide

/-- The `{\u00b12,\u00b13}` long support gives a six-regular exterior-pair model. -/
theorem sixTenLow_exteriorPairDegree (x : SixTenVertex) :
    sixTenExteriorPairDegree sixTenLowDefectAdj x = 6 := by
  revert x
  decide

/-- In the `{\u00b13,\u00b14}` branch every long vertex has exterior-pair degree
only four: three opposite-sign short vertices and its long antipode. -/
theorem sixTenHigh_long_exteriorPairDegree (i : ZMod 10) :
    sixTenExteriorPairDegree sixTenHighDefectAdj (Sum.inr i) = 4 := by
  revert i
  decide

/-- Short vertices retain exterior-pair degree six in the high branch; the
degree failure is confined exactly to the long shore. -/
theorem sixTenHigh_short_exteriorPairDegree (i : ZMod 6) :
    sixTenExteriorPairDegree sixTenHighDefectAdj (Sum.inl i) = 6 := by
  revert i
  decide

end Erdos85

#print axioms Erdos85.sixTenLow_exteriorPairDegree
#print axioms Erdos85.sixTenHigh_long_exteriorPairDegree
#print axioms Erdos85.sixTenHigh_short_exteriorPairDegree
#print axioms Erdos85.sixTenLow_short_exteriorPairAdj_iff
#print axioms Erdos85.sixTenLow_cross_exteriorPairAdj_iff
#print axioms Erdos85.sixTenLow_long_exteriorPairAdj_iff
#print axioms Erdos85.sixTenHigh_short_exteriorPairAdj_iff
#print axioms Erdos85.sixTenHigh_cross_exteriorPairAdj_iff
#print axioms Erdos85.sixTenHigh_long_exteriorPairAdj_iff
