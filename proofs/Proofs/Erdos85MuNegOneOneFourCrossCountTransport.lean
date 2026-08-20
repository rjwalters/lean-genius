import Mathlib

/-!
# Cross-complement count transport for the `mu=-1`, `(1,4)` bridge

Node: outline F.3, graph-to-finite-semantics instantiation (3c-i).

The exterior-pair graph has two edges in each four-element sign class.
The certificate relation `D` is its complement on the cross block, so it
also has two entries in each class.  This file isolates that Boolean count
step from the graph/ZMod enumeration and sign-coherence bookkeeping.
-/

namespace Erdos85

private theorem countP_add_countP_not
    {A : Type*} (l : List A) (p : A → Bool) :
    l.countP p + l.countP (fun x ↦ !p x) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases hp : p a <;> simp [hp] <;> omega

/-- Complementing a predicate inside a four-element Boolean class preserves
the value two.  Stating the lemma with `countP` makes it directly consumable
by `MuNegOneOneFourFiniteSemantics`. -/
theorem countP_not_eq_two_of_class_four_of_pos_two
    {A : Type*} (l : List A) (cls edge : A → Bool)
    (hclass : (l.filter cls).length = 4)
    (hpos : (l.filter cls).countP edge = 2) :
    (l.filter cls).countP (fun x ↦ !edge x) = 2 := by
  have hsum := countP_add_countP_not (l.filter cls) edge
  omega

/-- Row form of the cross-complement transport. -/
theorem muNegOne_crossComplement_row_count
    (R same : Nat → Bool)
    (hclass : ((List.range 8).filter same).length = 4)
    (hedge : ((List.range 8).filter same).countP R = 2) :
    ((List.range 8).filter same).countP (fun j ↦ !R j) = 2 :=
  countP_not_eq_two_of_class_four_of_pos_two (List.range 8) same R hclass hedge

/-- Column form of the same transport (kept as a named theorem so the
graph-facing assembly does not need to reshape row lemmas manually). -/
theorem muNegOne_crossComplement_col_count
    (R same : Nat → Bool)
    (hclass : ((List.range 8).filter same).length = 4)
    (hedge : ((List.range 8).filter same).countP R = 2) :
    ((List.range 8).filter same).countP (fun i ↦ !R i) = 2 :=
  countP_not_eq_two_of_class_four_of_pos_two (List.range 8) same R hclass hedge

end Erdos85

#print axioms Erdos85.countP_not_eq_two_of_class_four_of_pos_two
#print axioms Erdos85.muNegOne_crossComplement_row_count
#print axioms Erdos85.muNegOne_crossComplement_col_count
