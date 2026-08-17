import Proofs.Erdos85OrderSixtyFourTenSixEncoding

/-! # Semantics of the row-mask CNFs used by the order-64 census

`emit_r_completeness_cnf` enumerates every Boolean mask on the variables in
one integer row.  Whenever the mask violates the row bounds, it emits the
single clause having the opposite polarity at every position.  The lemmas
below prove that generic encoding step once, independently of the concrete
`[10,6]` row list.
-/

namespace Erdos85

open Std Sat

/-- The bit read by Python's `mask & (1 << offset)` convention. -/
def rowMaskBit (mask offset : Nat) : Bool := decide (mask.testBit offset)

/-- Clause excluding exactly one Boolean mask, with an explicit bit offset
so induction over the ordered key list preserves Python's numbering. -/
def rowMaskExclusionAux : List Nat → Nat → Nat → CNF.Clause Nat
  | [], _mask, _offset => []
  | key :: keys, mask, offset =>
      (key, !(rowMaskBit mask offset)) ::
        rowMaskExclusionAux keys mask (offset + 1)

def rowMaskExclusion (keys : List Nat) (mask : Nat) : CNF.Clause Nat :=
  rowMaskExclusionAux keys mask 0

/-- A valuation agrees with the selected mask at every ordered row key. -/
def RowMaskMatchesAux (val : Nat → Bool) : List Nat → Nat → Nat → Prop
  | [], _mask, _offset => True
  | key :: keys, mask, offset =>
      val key = rowMaskBit mask offset ∧
        RowMaskMatchesAux val keys mask (offset + 1)

def RowMaskMatches (val : Nat → Bool) (keys : List Nat) (mask : Nat) : Prop :=
  RowMaskMatchesAux val keys mask 0

/-- The emitted clause is false exactly on the mask it excludes. -/
theorem rowMaskExclusionAux_eval_eq_false_iff
    (val : Nat → Bool) (keys : List Nat) (mask offset : Nat) :
    CNF.Clause.eval val (rowMaskExclusionAux keys mask offset) = false ↔
      RowMaskMatchesAux val keys mask offset := by
  induction keys generalizing offset with
  | nil => simp [rowMaskExclusionAux, RowMaskMatchesAux, CNF.Clause.eval]
  | cons key keys ih =>
      simp only [rowMaskExclusionAux, RowMaskMatchesAux,
        CNF.Clause.eval_cons]
      rw [Bool.or_eq_false_iff, ih]
      cases hv : val key <;> cases hb : rowMaskBit mask offset <;> simp_all

theorem rowMaskExclusion_eval_eq_false_iff
    (val : Nat → Bool) (keys : List Nat) (mask : Nat) :
    CNF.Clause.eval val (rowMaskExclusion keys mask) = false ↔
      RowMaskMatches val keys mask := by
  exact rowMaskExclusionAux_eval_eq_false_iff val keys mask 0

/-- Integer value of a row on an actual Boolean valuation. -/
def booleanRowValue (coeff : Nat → Int) (val : Nat → Bool) : List Nat → Int
  | [] => 0
  | key :: keys => (if val key then coeff key else 0) +
      booleanRowValue coeff val keys

/-- Integer value of the same row on an enumerated mask. -/
def maskedRowValueAux (coeff : Nat → Int) : List Nat → Nat → Nat → Int
  | [], _mask, _offset => 0
  | key :: keys, mask, offset =>
      (if rowMaskBit mask offset then coeff key else 0) +
        maskedRowValueAux coeff keys mask (offset + 1)

def maskedRowValue (coeff : Nat → Int) (keys : List Nat) (mask : Nat) : Int :=
  maskedRowValueAux coeff keys mask 0

/-- Matching a mask preserves the integer row value, including negative and
non-unit coefficients used by the commutator rows. -/
theorem booleanRowValue_eq_maskedRowValueAux_of_matches
    (coeff : Nat → Int) (val : Nat → Bool) (keys : List Nat)
    (mask offset : Nat) (h : RowMaskMatchesAux val keys mask offset) :
    booleanRowValue coeff val keys =
      maskedRowValueAux coeff keys mask offset := by
  induction keys generalizing offset with
  | nil => rfl
  | cons key keys ih =>
      rcases h with ⟨hkey, hrest⟩
      simp only [booleanRowValue, maskedRowValueAux]
      rw [hkey, ih (offset := offset + 1) hrest]

theorem booleanRowValue_eq_maskedRowValue_of_matches
    (coeff : Nat → Int) (val : Nat → Bool) (keys : List Nat) (mask : Nat)
    (h : RowMaskMatches val keys mask) :
    booleanRowValue coeff val keys = maskedRowValue coeff keys mask :=
  booleanRowValue_eq_maskedRowValueAux_of_matches coeff val keys mask 0 h

/-- Soundness of one generated invalid-mask clause: any valuation whose
actual row value lies in bounds satisfies the clause excluding a mask whose
row value lies outside those bounds. -/
theorem rowMaskExclusion_eval_true_of_bounds
    (coeff : Nat → Int) (val : Nat → Bool) (keys : List Nat) (mask : Nat)
    (lower upper : Int)
    (hactual : lower ≤ booleanRowValue coeff val keys ∧
      booleanRowValue coeff val keys ≤ upper)
    (hinvalid : maskedRowValue coeff keys mask < lower ∨
      upper < maskedRowValue coeff keys mask) :
    CNF.Clause.eval val (rowMaskExclusion keys mask) = true := by
  cases heval : CNF.Clause.eval val (rowMaskExclusion keys mask) with
  | true => rfl
  | false =>
      have hmatch :=
        (rowMaskExclusion_eval_eq_false_iff val keys mask).mp heval
      have heq := booleanRowValue_eq_maskedRowValue_of_matches
        coeff val keys mask hmatch
      omega

/-- All masks on a row that violate its inclusive integer bounds. -/
def invalidRowMasks (coeff : Nat → Int) (keys : List Nat)
    (lower upper : Int) : List Nat :=
  (List.range (2 ^ keys.length)).filter fun mask =>
    decide (maskedRowValue coeff keys mask < lower ∨
      upper < maskedRowValue coeff keys mask)

/-- Exact clause block emitted for one bounded integer row. -/
def rowBoundCnf (coeff : Nat → Int) (keys : List Nat)
    (lower upper : Int) : CNF Nat where
  clauses := ((invalidRowMasks coeff keys lower upper).map
    (rowMaskExclusion keys)).toArray

/-- Soundness of a complete generated row block. -/
theorem rowBoundCnf_sat_of_bounds
    (coeff : Nat → Int) (keys : List Nat) (lower upper : Int)
    (val : Nat → Bool)
    (hactual : lower ≤ booleanRowValue coeff val keys ∧
      booleanRowValue coeff val keys ≤ upper) :
    (rowBoundCnf coeff keys lower upper).Sat val := by
  rw [CNF.sat_def, CNF.eval, Array.all_eq_true]
  intro j hj
  have hmemArray := Array.getElem_mem_toList
    (xs := (rowBoundCnf coeff keys lower upper).clauses) hj
  have hmemList :
      (rowBoundCnf coeff keys lower upper).clauses[j] ∈
        (invalidRowMasks coeff keys lower upper).map
          (rowMaskExclusion keys) := by
    simpa [rowBoundCnf] using hmemArray
  obtain ⟨mask, hmask, hclause⟩ := List.mem_map.mp hmemList
  have hinvalid : maskedRowValue coeff keys mask < lower ∨
      upper < maskedRowValue coeff keys mask := by
    simpa [invalidRowMasks] using (List.mem_filter.mp hmask).2
  rw [← hclause]
  exact rowMaskExclusion_eval_true_of_bounds coeff val keys mask
    lower upper hactual hinvalid

end Erdos85
