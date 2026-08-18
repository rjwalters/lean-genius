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

/-- Reference lookup of the internally zero-based DIMACS identifier of an
allowed pair. -/
def tenSixOutsideVarRaw? (i : Fin 6) (e f : Fin 48) : Option Nat :=
  let p := if e < f then (e, f) else (f, e)
  (tenSixOutsideAllowedPairs i).toList.idxOf? p

/-- Memoized variable lookup.  Clause generation calls this hundreds of
thousands of times, so materializing the finite `6 × 48 × 48` table avoids
repeating a linear `idxOf?` scan through up to 640 allowed pairs. -/
def tenSixOutsideVarTable : Array (Array (Array (Option Nat))) :=
  Array.ofFn fun i : Fin 6 =>
    Array.ofFn fun e : Fin 48 =>
      Array.ofFn fun f : Fin 48 => tenSixOutsideVarRaw? i e f

def tenSixOutsideVar? (i : Fin 6) (e f : Fin 48) : Option Nat :=
  ((tenSixOutsideVarTable.getD i.val #[]).getD e.val #[]).getD f.val none

/-- Closed audit that memoization does not change variable numbering. -/
theorem tenSixOutsideVar?_eq_raw : ∀ (i : Fin 6) (e f : Fin 48),
    tenSixOutsideVar? i e f = tenSixOutsideVarRaw? i e f := by
  intro i e f
  simp [tenSixOutsideVar?, tenSixOutsideVarTable]

theorem tenSixOutsideVar?_lt (i : Fin 6) (e f : Fin 48) {id : Nat}
    (h : tenSixOutsideVar? i e f = some id) :
    id < (tenSixOutsideAllowedPairs i).size := by
  rw [tenSixOutsideVar?_eq_raw] at h
  unfold tenSixOutsideVarRaw? at h
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
  rw [tenSixOutsideVar?_eq_raw] at hvar
  unfold tenSixOutsideVarRaw? at hvar
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

/-- Ordered `itertools.combinations(xs, 2)`. -/
def listPairs : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ listPairs xs

/-- IDs of all allowed C-neighbours `f` of `e` incident with inside vertex
`u`, in the generator's increasing `f` order. -/
def tenSixOutsideServiceTerms (i : Fin 6) (e : Fin 48) (u : Fin 16) :
    List Nat :=
  (List.finRange 48).filterMap fun f =>
    if tenSixIncidence i u f then tenSixOutsideVar? i e f else none

def tenSixOutsideServiceClausesAt
    (i : Fin 6) (e : Fin 48) (u : Fin 16) : List (CNF.Clause Nat) :=
  let terms := tenSixOutsideServiceTerms i e u
  if tenSixOutsideTarget i u e = 0 then
    terms.map fun id => [(id, false)]
  else
    [positiveClause terms] ++
      (listPairs terms).map fun p => [(p.1, false), (p.2, false)]

def tenSixOutsideServiceClauses (i : Fin 6) : List (CNF.Clause Nat) :=
  (List.finRange 48).flatMap fun e =>
    (List.finRange 16).flatMap fun u => tenSixOutsideServiceClausesAt i e u

/-- For fixed `a<b`, the two variable IDs witnessing common neighbour `c`. -/
def tenSixOutsideCommonTerms (i : Fin 6) (a b : Fin 48) :
    List (Nat × Nat) :=
  (List.finRange 48).filterMap fun c =>
    if c = a || c = b then none else
      match tenSixOutsideVar? i a c, tenSixOutsideVar? i b c with
      | some ac, some bc => some (ac, bc)
      | _, _ => none

def tenSixOutsideC4ClausesAt (i : Fin 6) (a b : Fin 48) :
    List (CNF.Clause Nat) :=
  (listPairs (tenSixOutsideCommonTerms i a b)).map fun p =>
    [(p.1.1, false), (p.1.2, false),
      (p.2.1, false), (p.2.2, false)]

def tenSixOutsideC4Clauses (i : Fin 6) : List (CNF.Clause Nat) :=
  tenSixOutsidePairs.toList.flatMap fun p =>
    tenSixOutsideC4ClausesAt i p.1 p.2

/-- Exact Lean reconstruction of the outside-C formula for model `i`. -/
def tenSixOutsideGeneratedCnf (i : Fin 6) : CNF Nat where
  clauses := (tenSixOutsideServiceClauses i ++
    tenSixOutsideC4Clauses i).toArray

def tenSixOutsideParsedCnf : Fin 6 → CNF Nat
  | ⟨0, _⟩ => tenSixC001Cnf
  | ⟨1, _⟩ => tenSixC002Cnf
  | ⟨2, _⟩ => tenSixC003Cnf
  | ⟨3, _⟩ => tenSixC004Cnf
  | ⟨4, _⟩ => tenSixC005Cnf
  | ⟨5, _⟩ => tenSixC006Cnf

end Erdos85
