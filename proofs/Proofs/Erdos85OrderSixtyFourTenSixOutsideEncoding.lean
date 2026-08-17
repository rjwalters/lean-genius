import Proofs.Erdos85OrderSixtyFourOutsideClauseEvaluation
import Proofs.Erdos85OrderSixtyFourTenSixOutsideUnsat
import Proofs.Erdos85OrderSixtyFourTenSixEncoding

/-! # Exact finite coordinates for the `[10,6]` outside-C formulas -/

namespace Erdos85

open Std Sat

/-- The Python `combinations(range(48), 2)` order. -/
def tenSixOutsidePairs : Array (Fin 48 × Fin 48) :=
  ((List.finRange 48).flatMap fun e =>
    ((List.finRange 48).filter fun f => e < f).map fun f => (e, f)).toArray

theorem tenSixOutsidePairs_size : tenSixOutsidePairs.size = 1128 := by
  native_decide

/-- The 48 exterior-pair edges in model `i`, in increasing 120-pair index
order—the exact outside-vertex order used by the certificate generator. -/
def tenSixRModelEdges (i : Fin 6) : Array (Fin 16 × Fin 16) :=
  ((tenSixRModelEdgeIndices i).map fun k =>
    tenSixPairs.getD k (0, 0)).toArray

theorem tenSixRModelEdges_size : ∀ i : Fin 6,
    (tenSixRModelEdges i).size = 48 := by
  native_decide

/-- Whether inside vertex `u` is an endpoint of outside vertex/`R`-edge `e`. -/
def tenSixIncidence (i : Fin 6) (u : Fin 16) (e : Fin 48) : Bool :=
  let p := (tenSixRModelEdges i)[e.val]'(by
    simpa [tenSixRModelEdges_size i] using e.isLt)
  decide (u = p.1 ∨ u = p.2)

/-- The certificate target `1 - H @ incidence`, computed in naturals. -/
def tenSixOutsideTarget (i : Fin 6) (u : Fin 16) (e : Fin 48) : Nat :=
  1 - ((List.finRange 16).filter fun k =>
    tenSixHAdj u k && tenSixIncidence i k e).length

theorem tenSixOutsideTarget_le_one : ∀ (i : Fin 6) (u : Fin 16) (e : Fin 48),
    tenSixOutsideTarget i u e ≤ 1 := by
  native_decide

/-- Candidate outside adjacency variables retained by the Python dominance
filter, before numbering. -/
def tenSixOutsideAllowed (i : Fin 6) (e f : Fin 48) : Bool :=
  decide (e < f) &&
    (List.finRange 16).all fun u =>
      ((!tenSixIncidence i u f) || decide (tenSixOutsideTarget i u e = 1)) &&
      ((!tenSixIncidence i u e) || decide (tenSixOutsideTarget i u f = 1))

/-- Allowed pairs, in the exact combinations order used for DIMACS IDs. -/
def tenSixOutsideAllowedPairs (i : Fin 6) : Array (Fin 48 × Fin 48) :=
  tenSixOutsidePairs.filter fun p => tenSixOutsideAllowed i p.1 p.2

/-- Closed audit of the six certificate variable counts. -/
theorem tenSixOutsideAllowedPairs_sizes :
    (List.finRange 6).map (fun i =>
      (tenSixOutsideAllowedPairs i).size) = [640, 640, 640, 640, 635, 635] := by
  native_decide

/-- Lookup the internally zero-based DIMACS identifier of an allowed pair. -/
def tenSixOutsideVar? (i : Fin 6) (e f : Fin 48) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (tenSixOutsideAllowedPairs i).toList.idxOf? p

theorem tenSixOutsideVar?_lt (i : Fin 6) (e f : Fin 48) {id : Nat}
    (h : tenSixOutsideVar? i e f = some id) :
    id < (tenSixOutsideAllowedPairs i).size := by
  unfold tenSixOutsideVar? at h
  split at h <;>
    simpa using (List.idxOf?_eq_some_iff.mp h).choose

/-- Boolean valuation induced by a candidate outside graph on `Fin 48`. -/
def tenSixOutsideDimacsValuation (i : Fin 6)
    (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj] : Nat → Bool := fun id =>
  if h : id < (tenSixOutsideAllowedPairs i).size then
    let p := (tenSixOutsideAllowedPairs i)[id]
    decide (C.Adj p.1 p.2)
  else false

/-- Lookup correctness for every allowed outside edge variable. -/
theorem tenSixOutsideDimacsValuation_var
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (e f : Fin 48) {id : Nat} (hvar : tenSixOutsideVar? i e f = some id) :
    tenSixOutsideDimacsValuation i C id = decide (C.Adj e f) := by
  have hid := tenSixOutsideVar?_lt i e f hvar
  rw [tenSixOutsideDimacsValuation, dif_pos hid]
  unfold tenSixOutsideVar? at hvar
  split at hvar
  next hef =>
    have hget := (List.idxOf?_eq_some_iff.mp hvar).choose_spec.1
    have hp : (tenSixOutsideAllowedPairs i)[id] = (e, f) := by
      simpa using hget
    rw [hp]
  next hef =>
    have hget := (List.idxOf?_eq_some_iff.mp hvar).choose_spec.1
    have hp : (tenSixOutsideAllowedPairs i)[id] = (f, e) := by
      simpa using hget
    rw [hp]
    simp only [C.adj_comm]

/-- The finite coordinate reconstruction agrees with all six parsed DIMACS
variable counts. -/
theorem tenSixOutsideParsed_numLiterals :
    tenSixC001Cnf.numLiterals = (tenSixOutsideAllowedPairs 0).size ∧
    tenSixC002Cnf.numLiterals = (tenSixOutsideAllowedPairs 1).size ∧
    tenSixC003Cnf.numLiterals = (tenSixOutsideAllowedPairs 2).size ∧
    tenSixC004Cnf.numLiterals = (tenSixOutsideAllowedPairs 3).size ∧
    tenSixC005Cnf.numLiterals = (tenSixOutsideAllowedPairs 4).size ∧
    tenSixC006Cnf.numLiterals = (tenSixOutsideAllowedPairs 5).size := by
  native_decide

end Erdos85
